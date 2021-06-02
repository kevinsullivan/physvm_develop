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
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    /*
    236-241
    try
    {
      geometry_msgs::TransformStamped target_to_planning_frame = transform_buffer_.lookupTransform(
          planning_frame_, target_pose_.header.frame_id, ros::Time(0), ros::Duration(0.1));
      tf2::doTransform(target_pose_, target_pose_, target_to_planning_frame);
    }


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
    
    //Declare a global Euclidean space, Time space, frame, measurement system
    //Declare a World frame and Base link frame

    std::string planning_frame_ = "Base Link";
    std::string target_pose_frame_ = "World";

    //Annotate this pose as being in the world frame
    //with a timestamp of now (or equivalence class of some sort) 
    tf2::Stamped<tf2::Pose> target_pose_before_;
    
    //Annotate this pose as being in the base link frame (after transform application),
    //with a timestamp of 0 (or equivalence class of some sort) 
    tf2::Stamped<tf2::Pose> target_pose_after_;
    target_pose_.frame_id = target_pose_frame_;

    //Annotate this transform as being from World->Base Link
    geometry_msgs::TransformStamped target_to_planning_frame = transform_buffer_.lookupTransform(
          planning_frame_, target_pose_before_.header.frame_id, ros::Time(0), ros::Duration(0.1));
        
    //This assignment is propagated automatically
    tf2::doTransform(target_pose_before_, target_pose_after_, target_to_planning_frame);

    //Annotate this timespan with a value of 1 second
    ros::Duration timespan = ros::Duration(1);

    //Annotate hasRecentTargetPose as being true, but annotate ros::Time::now() as being a fairly large value (>> 1), 
    //and Lean will need to calculate that this proposition evaluates to false.
    bool hasRecentTargetPose = ros::Time::now() - target_pose_.header.stamp).toSec() < timespan
}