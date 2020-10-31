#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include "nav_msgs/MapMetaData.h"
#include "nav_msgs/OccupancyGrid.h"
#include "nav_msgs/GetMap.h"

#include <cmath>

/*
Test 10.1 -  Simple Transformation Example


Description - This is a more elaborate (and arguably realistic) 
  example of a transformation construction and application.
  A transformation is constructed from a Quaternion and a Vector.
  This transformation is used to transform a vector from the 
  Map to the Robot frame.


Expected Outcome - 
Implementation Gaps - 
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
    Vectors and Points are not implemented in Lang
  -Layer 5 (CharlieLayer) :
*/

int main(int argc, char **argv){
    //Initialize the ROS node and retrieve a handle to it
    ros::init(argc, argv, "relative_frames");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry(3)
    //2 : @@ClassicalTime worldTime = ClassicalTime()
    //3 : @@ClassicalVelocity3 worldVelocity = ClassicalVelocity(worldGeometry, worldTime)
    //4 : @@MeasurementSystem si = SI()
    //5 : @@EuclideanGeometry3Frame stdWorldFrame = worldGeometry.stdFrame with si
    //6 : @@EuclideanGeometry3Frame robotFrame = EuclideanGeometry3Frame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>) with si

    ros::service::waitForService("/static_map");
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    nav_msgs::GetMap gm;

    cl.call(gm);

    //annotate this?
    nav_msgs::OccupancyGrid world_map = gm.response.map;
    
    //7: EuclideanGeometry3Orientation map_pose =  EuclideanGeometry3Orientation(worldGeometry, Value=<UNK>, stdWorldFrame,si)
    geometry_msgs::Pose map_pose = world_map.info.origin;
    
    //8: EuclideanGeometry3Orientation robot_pose_in_map = EuclideanGeometry3Orientation(worldGeometry, Value=<Position=<1, 1, 1>,Orientation=<UNK>>, stdWorldFrame,si)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.stamp = ros::Time::now();
    robot_pose_in_map.header.frame_id = world_map.header.frame_id;
    robot_pose_in_map.pose.position.x = 1;
    robot_pose_in_map.pose.position.y = 1;
    robot_pose_in_map.pose.position.z = 1;
    
    //9: @@EuclideanGeometry3Orientation map_to_robot_rotation = EuclideanGeometry3Orientation(worldGeometry, <origin=<computed>,orientation=<computed>>, stdWorldFrame,si)
    tf::Quaternion map_to_robot_rotation;
    map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
    map_to_robot_rotation.normalize();

    //10 : robot_pose_in_map.pose.orientation = map_to_robot_rotation
    tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);
    
    //11 : @@EuclideanGeometry3FrameTransform tf_map_to_robot_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->robotFrame)
    tf::StampedTransform tf_map_to_robot_transform(
        tf::Transform(
                tf::Quaternion(
                    robot_pose_in_map.pose.orientation.x,
                    robot_pose_in_map.pose.orientation.y,
                    robot_pose_in_map.pose.orientation.z,
                    robot_pose_in_map.pose.orientation.w
                ),
                tf::Vector3(
                    robot_pose_in_map.pose.position.x,
                    robot_pose_in_map.pose.position.y,
                    robot_pose_in_map.pose.position.z
                )
            ).inverse(),
        robot_pose_in_map.header.stamp,
        robot_pose_in_map.header.frame_id,
        "robot_base_link"
    );


    //12 : @@EuclideanGeometry3FrameTransform map_to_robot_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, <computed>, stdWorldFrame->robotFrame)
    geometry_msgs::TransformStamped map_to_robot_transform;

    //13 : map_to_robot_transform = tf_map_to_robot_transform
    tf::transformStampedTFToMsg(tf_map_to_robot_transform, map_to_robot_transform);

    //14: @@EuclideanGeometry3Orientation robot_origin_in_robot_frame = EuclideanGeometry3Orientation(worldGeometry->worldGeometry, <origin=<computed>, orientation=<computed>>,robotFrame,si)
    geometry_msgs::PoseStamped robot_origin_in_robot_frame;

    //15: ?
    tf2::doTransform(robot_pose_in_map, robot_origin_in_robot_frame, map_to_robot_transform);

    //16: @@ClassicalVelocity3Frame stdVel = worldVelocity.stdFrame with si
    //17: @@ClassicalVelocity3Frame robotVelFrame = ClassicalVelocity3Frame(worldVelocity, stdVel, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>)

    geometry_msgs::Vector3 
    //18: @@ClassicalVelocity3Vector robot_speed_in_map = ClassicalVelocity3Vector(worldVelocity, Value=<1,1,1>, stdVel,si)
                  robot_speed_in_map, 
    //19: @@ClassicalVelocity3Vector robot_speed_in_robot = ClassicalVelocity3Vector(worldVelocity, Value=<UNK>, stdVel,si)
                  robot_speed_in_robot;
    robot_speed_in_map.x = 1;
    robot_speed_in_map.y = 1;
    robot_speed_in_map.z = 1;

    //assignment occurs here
    tf2::doTransform(robot_speed_in_map, robot_speed_in_robot, map_to_robot_transform);
}