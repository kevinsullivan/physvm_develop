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
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    /*
    275-282

    geometry_msgs::PoseWithCovarianceStamped transformed_message;
    transformed_message.header.frame_id = target_frame;

    if (!transformMessage(tf_buffer, pose, transformed_message))
    {
        ROS_ERROR_STREAM("Cannot create constraint from pose message with stamp " << pose.header.stamp);
        return false;
    }

    
    */

    /*
      if (target_frame.empty())
        {
            transformed_message = pose;
        }
        else
        {
            transformed_message.header.frame_id = target_frame;

            if (!transformMessage(tf_buffer, pose, transformed_message))
            {
            ROS_ERROR_STREAM("Cannot create constraint from pose message with stamp " << pose.header.stamp);
            return false;
            }
        }
    */

    tf::Pose target_one;
}