
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/LinearMath/Transform.h>
#include <tf/LinearMath/Vector3.h>
#include <tf/transform_datatypes.h>

#include <tf2_ros/transform_broadcaster.h>


/*
*   THIS FILE IS A ROS NODE
*    IT IMPLEMENTS A TF **BROADCASTER** (STANDARD METHOD FOR TRANSMITTING TF FRAMES) TO BE USED IN HELLOWORLD
*
*/





int main(int argc, char **argv)
{
    ros::init(argc, argv, "tf_broadcaster");
    ros::NodeHandle node;
    static tf2_ros::TransformBroadcaster tr_br;
    
    ros::Time start = ros::Time::now();

    //same as in tf_publisher.cpp file
    tf::Quaternion qone;
    qone.setRPY(-1.5, 0, 1.5);
    tf::Quaternion qtwo;
    qtwo.setRPY(0,-1.5,1.5);
    tf::Quaternion qthree;
    qthree.setRPY(1.5, -1.5, 0);
    tf::Vector3 vone(1, 1, 1);
    tf::Vector3 vtwo(2, 2, 2);
    tf::Vector3 vthree(3, 3, 3);
    tf::Transform tone(qone, vone);
    tf::Transform ttwo(qtwo, vtwo);
    tf::Transform tthree(qthree, vthree);

    geometry_msgs::TransformStamped t3s_one_two;
    t3s_one_two.header.frame_id = "one";
    t3s_one_two.child_frame_id = "two";
    tf::transformTFToMsg(tone, t3s_one_two.transform);

    geometry_msgs::TransformStamped t3s_two_one;
    t3s_two_one.header.frame_id = "two";
    t3s_two_one.child_frame_id = "one";
    tf::transformTFToMsg(ttwo, t3s_two_one.transform);

    geometry_msgs::TransformStamped t3s_one_three;
    t3s_one_three.header.frame_id = "one";
    t3s_one_three.child_frame_id = "three";
    tf::transformTFToMsg(tthree, t3s_one_three.transform);

    geometry_msgs::Transform t3_one_two;
    tf::transformTFToMsg(tone, t3_one_two);
    geometry_msgs::Transform t3_two_one;
    tf::transformTFToMsg(ttwo, t3_two_one);
    geometry_msgs::Transform t3_one_three;
    tf::transformTFToMsg(tthree, t3_one_three);

    tf::Transform faulty_one_eight = tone * ttwo;
    geometry_msgs::TransformStamped faulty;
    tf::transformTFToMsg(faulty_one_eight, faulty.transform);
    faulty.header.frame_id = "one";
    faulty.child_frame_id = "eight";

    
    tf::Transform one_nine = tone;
    geometry_msgs::TransformStamped dynamic_frame;
    tf::transformTFToMsg(one_nine, dynamic_frame.transform);
    dynamic_frame.header.frame_id = "one";
    dynamic_frame.header.stamp = start;
    dynamic_frame.child_frame_id = "ten";

    ROS_INFO("Publishing One->Nine Transform. This frame is non-static and will update after 5 seconds");
    tr_br.sendTransform(dynamic_frame);

   // geometry_msgs::TransformStamped 
    
    ros::Rate timer(1000);

    int i = 0;
    bool update_dynamic = true;
    while(ros::ok())
    {
        timer.sleep();
        ros::Duration(1).sleep();

        if(i%4 == 0)
        {
            ROS_INFO("Publishing One->Two Transform");
            tr_br.sendTransform(t3s_one_two);
        }
        else if(i%4 == 1){
            ROS_INFO("Publishing Two->One Transform");

            //this can trigger a loop error. 
           // tr_br.sendTransform(t3s_two_one);
        }
        else if(i%4 == 2){
            ROS_INFO("Publishing faulty One->Eight Transform");
            tr_br.sendTransform(faulty);
        }
        else{
            ROS_INFO("Publishing One->Three Transform");
            tr_br.sendTransform(t3s_one_three);
        }
        i++;

        if(ros::Time::now() > start + ros::Duration(7)){
            ROS_INFO("SENDING UPDATED!!!");
            dynamic_frame.header.stamp = ros::Time::now();
            tf::transformTFToMsg(ttwo, dynamic_frame.transform);
            tr_br.sendTransform(dynamic_frame);
            update_dynamic != update_dynamic;
        }
        else{
            ROS_INFO("Publishing One->Nine Transform. This frame is non-static and will update after 5 seconds");
            tr_br.sendTransform(dynamic_frame);
        }

    }
}