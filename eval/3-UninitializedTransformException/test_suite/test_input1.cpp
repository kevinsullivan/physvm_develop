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
A try catch block is used when trying to look up a transform, as is typical in ROS, 
however, if it fails to lookup the transform, execution does not stop, and this 
faulty transform is used. As even a minor deviation in a transform from its correct value 
can result in drastically different output than what is expected, this is an error.
*/
int main(int argc, char **argv){
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    //86-93
    /*
    tf::StampedTransform CamToOutput;
    try{
        tf_listener->waitForTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, ros::Duration(1.0));
        tf_listener->lookupTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, CamToOutput);
    }
    catch (tf::TransformException ex){
        ROS_ERROR("%s",ex.what());
        return;
    }

    200
	tf::Transform tagPoseOutput = CamToOutput * markerPose;
    */

    //Declare a global Euclidean space, frame, measurement system
    //Declare an Output and Camera frame
    
    //Annotate this variable as either having a Default value, a Set of values, an Optional value
    //Either approach ignores control flow.
    tf::Transform CamToOutput;
    /*
    try{
        tf_listener->waitForTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, ros::Duration(1.0));
        tf_listener->lookupTransform(output_frame, image_msg->header.frame_id, image_msg->header.stamp, CamToOutput);
    }
    catch (tf::TransformException ex){
        ROS_ERROR("%s",ex.what());
        return;
    }
    */
    //...
    //Annotate this vector as being in the Camera frame
    tf::Vector3 markerPoint;

    //This computation will automatically yield a type error, triggered at the transform application
    tf::Vector3 tagPoseOutput = CamToOutput * markerPoint;//type error
}