
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
Test 5.1 Successful Transform Composition 

Name - 
Description - 
    This tests the composition functionality of transforms. 
    The result of this composition is a success.
Expected Outcome -
    First we create several spaces and frames (including a derived robot and hand frame).
    Next, we create a pose for the robot and hand in terms of the map and robot, respectively.
    Then, we create transform from map->hand first 
    by creating a transform from map->robot, then by robot->hand, and then composing them.

Implementation Gaps - 
  -Layer 1 (Parsers) :
    I have not supported nav_msgs yet. But probably easy
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
    No Frames/Transforms
  -Layer 4 (Phys) :
    No Frames/Transforms
  -Layer 5 (CharlieLayer) :
    No Frames/Transforms
*/

int main(int argc, char **argv){
    //Initialize the ROS node and retrieve a handle to it
    ros::init(argc, argv, "relative_frames");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry worldGeometry =  EuclideanGeometryLiteral(3)
    //2 : @@ClassicalTime worldTime = ClassicalTimeLiteral()
    //3 : @@ClassicalVelocity worldVelocity = ClassicalVelocityLiteral(worldGeometry, worldTime)
    //4 : @@ClassicalAcceleration worldAcceleration = ClassicalAccelerationLiteral(worldGeometry, worldTime)
    //5 : @@ClassicalGeometryFrame stdWorldFrame = worldGeometry.stdFrame
    //6 : @@MeasurementSystem si = SI()
    //7 : @@ClassicalGeometryFrame robotFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>,si)
    //8 : @@ClassicalGeometryFrame handFrame = ClassicalGeometryFrame(worldGeometry, robotFrame, <origin=<3,3,3>,,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>,si)

    ros::service::waitForService("/static_map");
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    nav_msgs::GetMap gm;

    cl.call(gm);

    //annotate this?
    nav_msgs::OccupancyGrid world_map = gm.response.map;
    
    //9: EuclideanGeometryOrientation (worldGeometry, Value=<UNK>, stdWorldFrame)
    geometry_msgs::Pose map_pose = world_map.info.origin;
    
    //10: EuclideanGeometryOrientation (worldGeometry, Value=<Position=<1, 1, 1>,Orientation=<UNK>>, stdWorldFrame, si)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.stamp = ros::Time::now();
    robot_pose_in_map.header.frame_id = world_map.header.frame_id;
    robot_pose_in_map.pose.position.x = 1;
    robot_pose_in_map.pose.position.y = 1;
    robot_pose_in_map.pose.position.z = 1;
    
    //11: @@GeometricOrientation map_to_robot_rotation = GeometricOrientation(worldGeometry, <origin=<computed>,orientation=<computed>>,stdWorldFrame,si)
    tf::Quaternion map_to_robot_rotation;
    map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
    map_to_robot_rotation.normalize();

    //12 : robot_pose_in_map.pose.orientation = map_to_robot_rotation
    tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);
    
    //13 : @@GeometricFrameTransform tf_map_to_robot_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>,stdWorldFrame->robotFrame,si)
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
    
    //14: EuclideanGeometryOrientation (worldGeometry, Value=<Position=<3, 3, 3>,Orientation=<UNK>>, robotFrame,si)
    geometry_msgs::PoseStamped hand_pose_in_robot;
    hand_pose_in_robot.header.stamp = ros::Time::now();
    hand_pose_in_robot.header.frame_id = world_map.header.frame_id;
    hand_pose_in_robot.pose.position.x = 3;
    hand_pose_in_robot.pose.position.y = 3;
    hand_pose_in_robot.pose.position.z = 3;
    
    //15: @@GeometricOrientation robot_to_hand_rotation = GeometricOrientation(worldGeometry, <origin=<computed>,orientation=<computed>>, robotFrame,si)
    tf::Quaternion robot_to_hand_rotation;
    robot_to_hand_rotation.setRPY(-1.5, 0, 1.5);
    robot_to_hand_rotation.normalize();

    //16 : hand_pose_in_robot.pose.orientation = robot_to_hand_rotation
    tf::quaternionTFToMsg(robot_to_hand_rotation, hand_pose_in_robot.pose.orientation);
    
    //17 : @@GeometricFrameTransform tf_robot_to_hand_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>, robotFrame->handFrame,si)
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

    //17 : @@GeometricFrameTransform tf_robot_to_hand_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->handFrame,si)
    tf::Transform good_transform_composition = tf_map_to_robot_transform * tf_robot_to_hand_transform;
}