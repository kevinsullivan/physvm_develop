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

    geometry_msgs::PoseStamped msg;//Timestamped IMU message using hardware time

    msg.header.stamp = hardware_clock_time;//Fine assignment

    ros::Time _ros_time_base = ros::Time::now();//Offset In System time

    double stamp_added_bias = _ros_time_base.toSec() + msg.header.stamp.toSec();//Error occurs here - invalid addition
    
    msg.header.stamp = ros::Time(stamp_added_bias);//Error occurs here - invalid assignment

}