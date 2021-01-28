
/*
The standard ROS/tf tutorial program.

http://wiki.ros.org/navigation/Tutorials/RobotSetup/TF

*/

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
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    ros::Rate r(100);
   
    tf::TransformBroadcaster broadcaster;
   
     while(node.ok()){
       broadcaster.sendTransform(
         tf::StampedTransform(
           tf::Transform(tf::Quaternion(0, 0, 0, 1), tf::Vector3(0.1, 0.0, 0.2)),
           ros::Time::now(),"base_link", "base_laser"));
       r.sleep();
     }

     tf::TransformListener listener;
     geometry_msgs::PointStamped laser_point; //= geometry_msgs::PointStamped();
     laser_point.header.frame_id = "base_laser";
   
     //we'll just use the most recent transform available for our simple example
     laser_point.header.stamp = ros::Time();
   
     //just an arbitrary point in space
     laser_point.point.x = 1.0;
     laser_point.point.y = 0.2;
     laser_point.point.z = 0.0;
   
     try{
       geometry_msgs::PointStamped base_point;

      listener.transformPoint("base_link", laser_point, base_point); 
      //base_point = [hiddentransform[from laser to base]]*laser 
      //tf::StampedTransform laser_to_base;
      //listener.lookupTransform("base_link", "base_laser", ros::Time(0),laser_to_base);
      //tf::Stamped<tf::Point> laser_point_tf;
      //tf::Point laser_point_tf;
      //tf::pointStampedMsgToTF(laser_point,laser_point_tf);
      //tf::Stamped<tf::Point> base_point_tf = laser_to_base*laser_point_tf;
      //tf::Point base_point_tf = laser_to_base*laser_point_tf;
      //tf::pointStampedTFToMsg(base_point_tf,base_point);
      /*

      */


       //Andrew: Comment this line out, it's very bad (for now)
       //ROS_INFO("base_laser: (%.2f, %.2f. %.2f) -----> base_link: (%.2f, %.2f, %.2f) at time %.2f",
       //    laser_point.point.x, laser_point.point.y, laser_point.point.z,
       //    base_point.point.x, base_point.point.y, base_point.point.z, base_point.header.stamp.toSec());
     }
     catch(tf::TransformException& ex){
       //Andrew: Comment this line out, it's very bad (for now)
      // ROS_ERROR("Received an exception trying to transform a point from \"base_laser\" to \"base_link\": %s", ex.what());
     }
}