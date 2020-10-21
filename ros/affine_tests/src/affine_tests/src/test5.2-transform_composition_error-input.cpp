
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
Test 5.1

Name - 
Description - 
    This tests the composition functionality of transforms. 
    The result of this composition is a failure.
Expected Outcome -
    First we create several spaces and frames (including a derived robot and hand frame).
    Next, we create a pose for the robot and a fly, both in terms of the map.
    We create a transform from map->robot, then a map->fly, and we attempt to compose them, 
    which yields an error.

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
    //7 : @@ClassicalGeometryFrame robotFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>,si>)
    //8 : @@ClassicalGeometryFrame flyFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<3,3,3>,,basis=<<1,1,1>,<1,1,1>,<1,1,1>>,si>)

    ros::service::waitForService("/static_map");
    ros::ServiceClient cl = node.serviceClient<nav_msgs::GetMap>("/static_map");

    nav_msgs::GetMap gm;

    cl.call(gm);

    //annotate this?
    nav_msgs::OccupancyGrid world_map = gm.response.map;
    
    //9: EuclideanGeometryOrientation (worldGeometry, Value=<UNK>, stdWorldFrame,si)
    geometry_msgs::Pose map_pose = world_map.info.origin;
    
    //10: EuclideanGeometryOrientation (worldGeometry, Value=<Position=<1, 1, 1>,Orientation=<UNK>>, stdWorldFrame,si)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.stamp = ros::Time::now();
    robot_pose_in_map.header.frame_id = world_map.header.frame_id;
    robot_pose_in_map.pose.position.x = 1;
    robot_pose_in_map.pose.position.y = 1;
    robot_pose_in_map.pose.position.z = 1;
    
    //11: @@GeometricOrientation map_to_robot_rotation = GeometricOrientation(worldGeometry, <origin=<computed>,orientation=<computed>>, stdWorldFrame,si)
    tf::Quaternion map_to_robot_rotation;
    map_to_robot_rotation.setRPY(-1.5, 0, 1.5);
    map_to_robot_rotation.normalize();

    //12 : robot_pose_in_map.pose.orientation = map_to_robot_rotation
    tf::quaternionTFToMsg(map_to_robot_rotation, robot_pose_in_map.pose.orientation);
    
    //13 : @@GeometricFrameTransform tf_map_to_robot_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->robotFrame,si)
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
    
    //14: EuclideanGeometryOrientation (worldGeometry, Value=<Position=<3, 3, 3>,Orientation=<UNK>>, stdWorldFrame,si)
    geometry_msgs::PoseStamped fly_pose_in_map;
    fly_pose_in_map.header.stamp = ros::Time::now();
    fly_pose_in_map.header.frame_id = world_map.header.frame_id;
    fly_pose_in_map.pose.position.x = 3;
    fly_pose_in_map.pose.position.y = 3;
    fly_pose_in_map.pose.position.z = 3;
    
    //15: @@GeometricOrientation map_to_robot_rotation = GeometricOrientation(worldGeometry, <origin=<computed>,orientation=<computed>>, stdWorldFrame,si)
    tf::Quaternion map_to_fly_rotation;
    map_to_fly_rotation.setRPY(-1.5, 0, 1.5);
    map_to_fly_rotation.normalize();

    //16 : fly_pose_in_map.pose.orientation = map_to_fly_rotation
    tf::quaternionTFToMsg(map_to_fly_rotation, fly_pose_in_map.pose.orientation);
    
    //17 : @@GeometricFrameTransform tf_map_to_fly_transform = GeometricFrameTransform(worldGeometry->worldGeometry, Value=<computed>, stdWorldFrame->robotFrame,si)
    tf::StampedTransform tf_map_to_fly_transform(
        tf::Transform(
                tf::Quaternion(
                    fly_pose_in_map.pose.orientation.x,
                    fly_pose_in_map.pose.orientation.y,
                    fly_pose_in_map.pose.orientation.z,
                    fly_pose_in_map.pose.orientation.w
                ),
                tf::Vector3(
                    fly_pose_in_map.pose.position.x,
                    fly_pose_in_map.pose.position.y,
                    fly_pose_in_map.pose.position.z
                )
            ).inverse(),
        fly_pose_in_map.header.stamp,
        fly_pose_in_map.header.frame_id,
        "fly"
    );

    //18 (ERROR!) : @@GeometricFrameTransform...
    tf::Transform bad_transform = tf_map_to_robot_transform * tf_map_to_fly_transform;

}