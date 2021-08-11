# Take 2

## IGNORE FOR NOW

The C++ code for which we need an interpretation is as follows:

```c++
ros::Time hardware_clock_time = getHardwareTime();
```
The *hardware_clock_time* variable, of type ros::Time, represents the current point in time according to the a hardware component of interest. This variable thus stores a pair of int32 values, for seconds and nanoseconds elapsed since an origin point in time. We don't currently know what the hardware component is or what origin is assumes when representing time. 


Note: ros::duration has the same representation. See the actual ROS type definitions to see if they're just typedefs, in which case there can be no enforcement of affine space operations, or actually different C++ types. See <http://wiki.ros.org/roscpp/Overview/Time> for the definition of the ros::Time type and <https://docs.ros.org/en/latest/api/rostime/html/classros_1_1TimeBase.html#details> for details of operations involving times and durations. Also, for documentation on time arithmetic, see <http://wiki.ros.org/action/fullsearch/roscpp/Overview/Time?action=fullsearch&context=180&value=linkto%3A%22roscpp%2FOverview%2FTime%22>.

``` c++
    geometry_msgs::PoseStamped msg;
```
The *msg* variable, of type *geometry_msgs::PoseStamped*, will store a timestamped IMU message using hardware time.

``` c++
    msg.header.stamp = hardware_clock_time;//Fine assignment

    ros::Time _ros_time_base = getSystemTime();//Offset In System time
    ros::Time ros_time_base_alias = _ros_time_base;//Time in System Coordinate Space
    double ros_time_base_coord = ros_time_base_alias.toSec();
    //Coordinate of a Time After Unit Transformation From System CS to a Space With Seconds as a Unit
    
    /*
    1. Mapping from Point to Vector (Time to Duration)
    2. Transform to new Coordinate Space (System CS to System-Seconds CS)
    3. Extraction of a Coordinate (from Vector in SysSecCS to Coordinate SysSecCS)
*/
    ros::Time msg_stamp_alias = 
    double msg_coord = msg.header.stamp.toSec();

    double stamp_added_bias = ros_time_base_coord + msg_coord

    msg.header.stamp = ros::Time(stamp_added_bias);//Error occurs here - invalid assignment
```

