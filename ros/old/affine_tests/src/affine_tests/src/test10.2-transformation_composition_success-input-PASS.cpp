
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
Test 10.1 - Successful Transform Composition 


Description - 
    This test demonstrates the successful composition 
    of two transformations together, one from map to robot,
    multiplied by another from robot to the left hand.


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
    //4 : @@ClassicalAcceleration3 worldAcceleration = ClassicalAcceleration(worldGeometry, worldTime)
    //5 : @@EuclideanGeometry3Frame stdWorldFrame = worldGeometry.stdFrame with si
    //6 : @@MeasurementSystem si = SI()
    //7 : @@EuclideanGeometry3Frame robotFrame = EuclideanGeometry3Frame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>) with si
    //8 : @@EuclideanGeometry3Frame handFrame = EuclideanGeometry3Frame(worldGeometry, robotFrame, <origin=<3,3,3>,,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>) with si

    ros::service::waitForService("/static_map");
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    nav_msgs::GetMap gm;

    cl.call(gm);

    //annotate this?
    nav_msgs::OccupancyGrid world_map = gm.response.map;
    
    //9: EuclideanGeometry3Orientation map_pose = EuclideanGeometry3Orientation(worldGeometry, Value=<UNK>, stdWorldFrame)
    geometry_msgs::Pose map_pose = world_map.info.origin;
    
    //10: EuclideanGeometry3Orientation robot_pose_in_map = EuclideanGeometry3Orientation(worldGeometry, Value=<Position=<1, 1, 1>,Orientation=<UNK>>, stdWorldFrame)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.stamp = ros::Time::now();
    robot_pose_in_map.header.frame_id = world_map.header.frame_id;
    robot_pose_in_map.pose.position.x = 1;
    robot_pose_in_map.pose.position.y = 1;
    robot_pose_in_map.pose.position.z = 1;
    
    //11: @@EuclideanGeometry3Orientation map_to_robot_rotation = EuclideanGeometry3Orientation(worldGeometry, <origin=<computed>,orientation=<computed>>,stdWorldFrame)
    tf::Quaternion map_to_robot_rotation;
    map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
    map_to_robot_rotation.normalize();

    //12 : robot_pose_in_map.pose.orientation = map_to_robot_rotation
    tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);
    
    //13 : @@EuclideanGeometry3FrameTransform tf_map_to_robot_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, Value=<computed>,stdWorldFrame->robotFrame)
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
    
    //14: EuclideanGeometry3Orientation (worldGeometry, Value=<Position=<3, 3, 3>,Orientation=<UNK>>, robotFrame)
    geometry_msgs::PoseStamped hand_pose_in_robot;
    hand_pose_in_robot.header.stamp = ros::Time::now();
    hand_pose_in_robot.header.frame_id = world_map.header.frame_id;
    hand_pose_in_robot.pose.position.x = 3;
    hand_pose_in_robot.pose.position.y = 3;
    hand_pose_in_robot.pose.position.z = 3;
    
    //15: @@EuclideanGeometry3Orientation robot_to_hand_rotation = EuclideanGeometry3Orientation(worldGeometry, <origin=<computed>,orientation=<computed>>, robotFrame)
    tf::Quaternion robot_to_hand_rotation;
    robot_to_hand_rotation.setRPY(-1.5, 0, 1.5);
    robot_to_hand_rotation.normalize();

    //16 : hand_pose_in_robot.pose.orientation = robot_to_hand_rotation
    tf::quaternionTFToMsg(robot_to_hand_rotation, hand_pose_in_robot.pose.orientation);
    
    //17 : @@EuclideanGeometry3FrameTransform tf_robot_to_hand_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, Value=<computed>, robotFrame->handFrame)
    tf::StampedTransform tf_robot_to_hand_transform(
        tf::Transform(
                tf::Quaternion(
                    hand_pose_in_robot.pose.orientation.x,
                    hand_pose_in_robot.pose.orientation.y,
                    hand_pose_in_robot.pose.orientation.z,
                    hand_pose_in_robot.pose.orientation.w
                ),
                tf::Vector3(
                    hand_pose_in_robot.pose.position.x,
                    hand_pose_in_robot.pose.position.y,
                    hand_pose_in_robot.pose.position.z
                )
            ).inverse(),
        hand_pose_in_robot.header.stamp,
        hand_pose_in_robot.header.frame_id,
        "robot_hand"
    );

    //17 : @@EuclideanGeometry3FrameTransform tf_robot_to_hand_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->handFrame)
    tf::Transform good_transform_composition = tf_map_to_robot_transform * tf_robot_to_hand_transform;
}