
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

    //Dr Sullivan comment:
    /*
    Annotate this entire piece of code to assume that we are working in geometric space.
    Let the space be called s3d = (p3d, v3d)
    Let f3d be the standard frame on s3d
    f3d = (std_p, std_v_0, std_v_1, std_v_2)

    */
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

    //TIME EXAMPLE, 6/19/20:
    geometry_msgs::PointStamped startpt, endpt;
    ros::Time starttm, endtm;

    startpt.point.x = 10; startpt.point.y = 10; startpt.point.z = 10; 
    startpt.header.frame_id = "standard";
    starttm = ros::Time::now() - ros::Duration(10);

    endpt.point.x = 20; endpt.point.y = -2; endpt.point.z = 12;
    endpt.header.frame_id = "standard";
    endtm = ros::Time::now();

    tf2::Vector3 travelled(
        endpt.point.x - startpt.point.x,
        endpt.point.y - startpt.point.y,
        endpt.point.z - startpt.point.z
    );

    tf2::Vector3 velocity = travelled/(endtm - starttm).toSec();

    geometry_msgs::Vector3 gd, gv;
    gd = tf2::toMsg(travelled);
    gv = tf2::toMsg(velocity);

    ROS_INFO("Start:");
    ROS_INFO_STREAM(startpt);
    ROS_INFO("End");
    ROS_INFO_STREAM(endpt);
    ROS_INFO("Coordinate-wise distance travelled:");
    ROS_INFO_STREAM(gd);
    ROS_INFO("Velocity over 5 seconds:");
    ROS_INFO_STREAM(gv);

    

}
