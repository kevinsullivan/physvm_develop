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
Test 5

Name -  Simple Transformation Example
Description - 
    This depicts the construction of a transformation from a pose, as well as a transformation
    of a velocity vector from one frame into another.

Expected Outcome -
    Several spaces are defined. A map is retrieved. 
    A robot's pose is established in terms of the map. The pose is used to create a transform
    into the perspective of the robot. 
    We define the robot's velocity in terms of the map. We apply the transform, which 
    gives us a vector expressed in terms of the robot.

Implementation Gaps - 
  -Layer 1 (Parsers) :
    I have not supported nav_msgs yet. But probably easy
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
    No Frames/Transforms/Poses/Angles/Quaternions
  -Layer 4 (Phys) :
    No Frames/Transforms/Poses/Angles/Quaternions
  -Layer 5 (CharlieLayer) :
    No Frames/Transforms/Poses/Angles/Quaternions
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
    //6 : @@ClassicalGeometryFrame robotFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>)
    //7 : @@MeasurementSystem si = SI()

    ros::service::waitForService("/static_map");
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    nav_msgs::GetMap gm;

    cl.call(gm);

    //annotate this?
    nav_msgs::OccupancyGrid world_map = gm.response.map;
    
    //7: EuclideanGeometryOrientation (worldGeometry, Value=<UNK>, stdWorldFrame,si)
    geometry_msgs::Pose map_pose = world_map.info.origin;
    
    //8: EuclideanGeometryOrientation (worldGeometry, Value=<Position=<1, 1, 1>,Orientation=<UNK>>, stdWorldFrame,si)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.stamp = ros::Time::now();
    robot_pose_in_map.header.frame_id = world_map.header.frame_id;
    robot_pose_in_map.pose.position.x = 1;
    robot_pose_in_map.pose.position.y = 1;
    robot_pose_in_map.pose.position.z = 1;
    
    //9: @@GeometricOrientation map_to_robot_rotation = GeometricOrientation(worldGeometry, <origin=<computed>,orientation=<computed>>, stdWorldFrame,si)
    tf::Quaternion map_to_robot_rotation;
    map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
    map_to_robot_rotation.normalize();

    //10 : robot_pose_in_map.pose.orientation = map_to_robot_rotation
    tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);
    
    //11 : @@GeometricFrameTransform tf_map_to_robot_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->robotFrame)
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


    //12 : @@GeometricFrameTransform map_to_robot_transform = GeometricFrameTransform(worldGeometry->worldGeometry, <computed>, stdWorldFrame->robotFrame)
    geometry_msgs::TransformStamped map_to_robot_transform;

    //13 : map_to_robot_transform = tf_map_to_robot_transform
    tf::transformStampedTFToMsg(tf_map_to_robot_transform, map_to_robot_transform);

    //14: @@GeometricOrientation robot_origin_in_robot_frame = GeometricOrientation(worldGeometry->worldGeometry, <origin=<computed>, orientation=<computed>>,robotFrame,si)
    geometry_msgs::PoseStamped robot_origin_in_robot_frame;

    //15: ?
    tf2::doTransform(robot_pose_in_map, robot_origin_in_robot_frame, map_to_robot_transform);

    //16: @@ClassicalVelocityFrame stdVel = worldVelocity.stdFrame
    //17: @@ClassicalVelocityFrame robotVelFrame = ClassicalVelocityFrame(worldVelocity, stdVel, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>)

    geometry_msgs::Vector3 
    //18: @@ClassicalVelocityVector robot_speed_in_map = ClassicalVelocityVector(worldVelocity, Value=<1,1,1>, stdVel,si)
                  robot_speed_in_map, 
    //19: @@ClassicalVelocityVector robot_speed_in_robot = ClassicalVelocityVector(worldVelocity, Value=<UNK>, stdVel,si)
                  robot_speed_in_robot;
    robot_speed_in_map.x = 1;
    robot_speed_in_map.y = 1;
    robot_speed_in_map.z = 1;

    //assignment occurs here
    tf2::doTransform(robot_speed_in_map, robot_speed_in_robot, map_to_robot_transform);
}