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
/*
When looking up a transform, if there is a static transform available between two frames, 
it may assign a timestamp of 0 to the resulting pose, which may indicate that the transform 
is old, but is misleading to consumers of this pose, as it is technically using a recent 
(and old, concurrently) version of the transform.
*/
int main(int argc, char **argv){
    //ros::init(argc, argv, " ");
    //ros::NodeHandle node;  

    /*
    236-241
    try
    {
      geometry_msgs::TransformStamped target_to_planning_frame = transform_buffer_.lookupTransform(
          planning_frame_, target_pose_.header.frame_id, ros::Time(0), ros::Duration(0.1));
      tf2::doTransform(target_pose_, target_pose_, target_to_planning_frame);
    }
3

    206-210
    bool PoseTracking::haveRecentTargetPose(const double timespan)
    {
    std::lock_guard<std::mutex> lock(target_pose_mtx_);
    return ((ros::Time::now() - target_pose_.header.stamp).toSec() < timespan);
    }

    85-93
    while ((!haveRecentTargetPose(target_pose_timeout) || !haveRecentEndEffectorPose(target_pose_timeout)) &&
         ((ros::Time::now() - start_time).toSec() < target_pose_timeout))
    {
        if (servo_->getCommandFrameTransform(command_frame_transform_))
        {
        command_frame_transform_stamp_ = ros::Time::now();
        }
        ros::Duration(0.001).sleep();
    }
    */
    
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