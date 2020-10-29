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
Test 10.0 -  Simple Transformation Example


Description - This example defines a transformation without any 
    explicit value available in the code (may be the case in real ROS code).
    This transformation is used to transform a value in the map frame 
    to the robot frame.
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

    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometryLiteral(3)
    //2 : @@MeasurementSystem si = SI()
    //3 : @@EuclideanGeometry3Frame stdWorldFrame = worldGeometry.stdFrame with si
    //4 : @@EuclideanGeometry3Frame robotFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>) with si

    //5 : @@EuclideanGeometry3Pose robot_pose_in_map = EuclideanGeometry3Pose(worldGeometry, <UNK>,worldStdFrame)
    geometry_msgs::PoseStamped robot_pose_in_map;
    robot_pose_in_map.header.frame_id = "map";

    //6 : @@EuclideanGeometry3Pose robot_pose_in_robot
    geometry_msgs::PoseStamped robot_pose_in_robot;

    //7 : @@EuclideanGeometry3FrameTransform map_to_robot_transform = EuclideanGeometry3FrameTransform(worldGeometry->worldGeometry, <computed>, stdWorldFrame->robotFrame)
    geometry_msgs::TransformStamped map_to_robot_transform;
    map_to_robot_transform.header.frame_id = "map";
    map_to_robot_transform.child_frame_id = "robot";

    //8 : @@robot_pose_in_robot = EuclideanGeometry3Pose(worldGeometry,<>,robotFrame)
    tf2::doTransform(robot_pose_in_map, robot_pose_in_robot, map_to_robot_transform);

}