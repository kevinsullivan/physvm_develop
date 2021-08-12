# Detailed analysis of original code. What is it actually doing?

``` c++
void BaseRealSenseNode::imu_callback_sync(rs2::frame frame, imu_sync_method sync_method)
/*
rs2::frame frame (not a tf frame) represents a timestamped image
coming from a RealSense imager (camera). For us the main point is
that it comes with a time stamp, returned as a double.

https://dev.intelrealsense.com/docs/frame-metadata
*/  
{
    static std::mutex m_mutex;
    static int seq = 0;

    m_mutex.lock();

    //Stream data expected to come from Gyroscope or Accelerometer
    auto stream = frame.get_profile().stream_type();
    auto stream_index = (stream == GYRO.first)?GYRO:ACCEL;

    /*
    Here's the line where we get the timestamp for the image.
    It comes back as a double, representing a time at which an
    image frame was acquired. See the documentation for details.
    https://docs.ros.org/en/kinetic/api/librealsense2/html/classrs2_1_1frame.html#ad2f1eceeed1e40e8f6c4ef2c42485532.
    We note that: while the units here are documented as ms,
    the origin of this time representation isn't entirely clear.
    */
    double frame_time = frame.get_timestamp();

    bool placeholder_false(false);
    if (_is_initialized_time_base.compare_exchange_strong(placeholder_false, true) )
    {
        //See line ~1700 discussed today
        /*
        This method will set the ros_time_base variable used to ros::time::now() and the camera_time_base to the value of frame_time.
        */
        setBaseTime(frame_time, frame.get_frame_timestamp_domain());
    }

    seq += 1;

    /*
    Here we calculate how long the camera has been running for, in milliseconds, relative to
    _camera_time_base, which appears to be set on the first time through this procedure, i.e., 
    probably on the first image frame that the camera captures. So *elapsed_camera_ms* represents
    a duration relative to camera acquisition start time.
    */
    double elapsed_camera_ms = (/*ms*/ frame_time - /*ms*/ _camera_time_base) / 1000.0;

    if (0 != _synced_imu_publisher->getNumSubscribers())
    {
        //extracts the value contained in the frame. most likely a gyroscope reading
        auto crnt_reading = *(reinterpret_cast<const float3*>(frame.get_data()));
        //convert this into eigen vector
        Eigen::Vector3d v(crnt_reading.x, crnt_reading.y, crnt_reading.z);
        //Create an object called CimuData. No side effects. Just stores arguments into properties.
        CimuData imu_data(stream_index, v, elapsed_camera_ms);
        std::deque<sensor_msgs::Imu> imu_msgs;
        switch (sync_method)
        {
            case NONE: //Cannot really be NONE. Just to avoid compilation warning.
            case COPY:
                /*
                If the data is a gyroscope reading, the rest of the method fails and control breaks through.
                If it's an accelerometer reading, copy the accelerometer reading into a new IMU message using the accel
                data for both the gyro and accel properties, with the timestamp of the frame, and add it to the imu_msgs data queue.

                Timestamp is elapsed_camera_ms
                */
                FillImuData_Copy(imu_data, imu_msgs);
                break;
            case LINEAR_INTERPOLATION:
                /*
                If the data is a gyroscope reading, the rest of the method fails and control breaks through.
                Also requires accel data history of 3 or else control breaks through.
                Essentially, it will iterate over every Gyroscope in between a previous pair of accelerometer messages, and then 
                create an IMU message with a simple interpolation between the two timestamps.

                Timestamp of each IMU message is set to each Gyroscope message
                */
                FillImuData_LinearInterpolation(imu_data, imu_msgs);
                break;
        }
        /*
        The COPY case will only populate one entry in imu_msgs, the LINEAR_INTERPOLATION case may publish many
        */
        while (imu_msgs.size()) 
        {
            sensor_msgs::Imu imu_msg = imu_msgs.front();
            /*
            Whether or not an error occurs here, as the issue plainly described, depends on execution context.
            _ros_time_base.toSec() may be a coordinate in System time, where as the imu_msg may be in the Camera Hardware Clock
            */;
            ros::Time t(_ros_time_base.toSec() + imu_msg.header.stamp.toSec());
            imu_msg.header.seq = seq;
            imu_msg.header.stamp = t;
            ImuMessage_AddDefaultValues(imu_msg);
            _synced_imu_publisher->Publish(imu_msg);
            ROS_DEBUG("Publish united %s stream", rs2_stream_to_string(frame.get_profile().stream_type()));
            imu_msgs.pop_front();
        }
    }
    m_mutex.unlock();
};

```