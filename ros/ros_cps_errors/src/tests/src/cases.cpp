
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>



int main(int argc, char **argv){
    ros::init(argc, argv, "cases");
    ros::NodeHandle node;

    geometry_msgs::Vector3Stamped two_vec_s;
    two_vec_s.vector.x = 2;
    two_vec_s.vector.y = 2;
    two_vec_s.vector.z = 2;
    /*
    Let "two" be an affine frame on s3d with coordinates with respect to the std frame
    */

    two_vec_s.header.frame_id = "two";

     //same as in tf_publisher.cpp file
    tf::Quaternion qone;
    qone.setRPY(-1.5, 0, 1.5);
    //{kilometers} -> 
    tf::Vector3 vone(1, 1, 1);//{length, {Real Affine 3 Space, frame two}, vector (not point)}
    tf::Transform tone(qone, vone);//{length, R^3, vector (not point), frame one} -> {length, R^3, vector (not point), frame two}

    geometry_msgs::TransformStamped t3s_one_two;//{length, R^3, vector (not point), frame one} -> {length, R^3, vector (not point), frame two}
    t3s_one_two.header.frame_id = "one";
    t3s_one_two.child_frame_id = "two";
    tf::transformTFToMsg(tone, t3s_one_two.transform);


    geometry_msgs::Vector3Stamped new_vec;//{length, R^3, vector (not point), frame two}
    tf2::doTransform(two_vec_s, new_vec, t3s_one_two);//result : {length, R^3, vector (not point), frame one} ! ERROR: frame new_vec <> result of transform

    ROS_ERROR("ARG FRAME : %s, TRANSFORM FRAME : %s -> %s, OUT FRAME %s", two_vec_s.header.frame_id.c_str(), t3s_one_two.header.frame_id.c_str(), t3s_one_two.child_frame_id.c_str(), new_vec.header.frame_id.c_str());
    
}