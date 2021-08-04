Issue:
  https://github.com/FS-Driverless/Formula-Student-Driverless-Simulator/pull/112

TEST 1:

Categorization:

File:
  ros/src/fsds_ros_bridge/src/airsim_ros_wrapper.cpp

Line:
  line 345

Commit: 3f84a48

Code:
  imu_msg.angular_velocity.x = imu_data.angular_velocity.x();
  imu_msg.angular_velocity.y = imu_data.angular_velocity.y();
  imu_msg.angular_velocity.z = imu_data.angular_velocity.z();

  // meters/s2^m
  imu_msg.linear_acceleration.x = imu_data.linear_acceleration.x();
  imu_msg.linear_acceleration.y = imu_data.linear_acceleration.y();
  imu_msg.linear_acceleration.z = imu_data.linear_acceleration.z();

Short Description: 
  

Error Location/Description: 

Changes in Peirce: 