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
#include <kdl_parser/kdl_parser.hpp>
#include <robot_state_publisher/robot_state_publisher.h>
#include <urdf/Model.h>
#include <cmath>
#include <chrono>
#include <threading>
/*
When looking up a transform, if there is a static transform available between two frames, 
it may assign a timestamp of 0 to the resulting pose, which may indicate that the transform 
is old, but is misleading to consumers of this pose, as it is technically using a recent 
(and old, concurrently) version of the transform.
*/
void publish_world_to_baselink(){
    KDL::Tree servotree;
    urdf::Model servomodel;
    servomodel.initFile("/peirce/ros_test_cases/eval/5-TimestampMismatch/test_suite/test_urdf.xacro");
    kdl_parser::treeFromUrdfModel(servomodel,servotree);
    robot_state_publisher::RobotStatePublisher servopub(servotree);

    while(true){
        servopub.publishFixedTransforms();
        std::this_thread->sleep_for(5000ms);
    }
};


int main(int argc, char **argv){
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    //Declare world time space, world space, base link space

    //Add a global time series 

    //Annotate as "Pose3D Time Series" - add an initial value
    geometry_msgs::PoseStamped target_pose_in_world;
    //target_pose_in_world.header.frame_id = planning_frame_;

    //Annotate 
    geometry_msgs::PoseStamped target_pose_in_base_link;

    //Annotate this transform as being from World->Base Link
    geometry_msgs::TransformStamped target_to_planning_frame; 
        
    //This assignment is propagated automatically. Target Pose in Base Link is updated
    tf2::doTransform(target_pose_in_world, target_pose_in_base_link, target_to_planning_frame);
////
    //Annotate this either as a scalar or a duration...
    double timespan = 1;

    //Annotate ros::Time::Now as having a value greater than 1. The toSec call can either be annotated as a 
    //case to a scalar, or ignored, depending on timespan annotation
    bool hasRecentTargetPose = (ros::Time::now() - target_pose_in_base_link.header.stamp).toSec() < timespan;
    //
}   