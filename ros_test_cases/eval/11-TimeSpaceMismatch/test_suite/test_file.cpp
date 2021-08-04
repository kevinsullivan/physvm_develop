#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <tf/transform_listener.h>
#include <tf/transform_broadcaster.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"


#include <cmath>


int main(int argc, char **argv){
/*  
Lean Issue:
noncomputable def wt_fr : time_frame_expr := |time_std_frame|
noncomputable def wt : time_space_expr wt_fr := |time_std_space|
noncomputable def wt2_fr : time_frame_expr := |time_std_frame|
noncomputable def wt2 : time_space_expr wt_fr := |time_std_space|

noncomputable def de : duration_expr wt := |mk_duration wt2.value 2|
*/

    ros::Time hardware_clock_time = ros::Time(1);//Time in hardware space

    sensor_msgs::Imu imu_msg;//Timestamped IMU message using hardware time

    imu_msg.stamp = ros::Time(hardware_clock_time);//Fine assignment

    ros::Time _ros_time_base = ros::Time::Now();//In System time

    ros::Time t(_ros_time_base.toSec() + imu_msg.header.stamp.toSec());//Error occurs here - invalid addition
    
    imu_msg.header.stamp = t;//Error occurs here - invalid assignment

}