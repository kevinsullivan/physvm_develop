
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/LinearMath/Transform.h>
#include <tf/LinearMath/Vector3.h>
#include <tf/transform_datatypes.h>


//add two vectors in different base

//transform vector in different base





int main(int argc, char **argv)
{
    ros::init(argc, argv, "tf_publisher");
    
    ros::NodeHandle node;

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


    auto trans_s_pub = node.advertise<geometry_msgs::TransformStamped>("/trans_s", 25000000);
    geometry_msgs::TransformStamped t3s_one_two;
    t3s_one_two.header.frame_id = "one";
    t3s_one_two.header.frame_id = "two";
    tf::transformTFToMsg(tone, t3s_one_two.transform);

    geometry_msgs::TransformStamped t3s_two_one;
    t3s_two_one.header.frame_id = "two";
    t3s_two_one.header.frame_id = "one";
    tf::transformTFToMsg(ttwo, t3s_two_one.transform);

    geometry_msgs::TransformStamped t3s_one_three;
    t3s_one_three.header.frame_id = "one";
    t3s_one_three.header.frame_id = "three";
    tf::transformTFToMsg(tthree, t3s_one_three.transform);


    auto trans_pub = node.advertise<geometry_msgs::Transform>("trans",25000000);
    geometry_msgs::Transform t3_one_two;
    tf::transformTFToMsg(tone, t3_one_two);
    geometry_msgs::Transform t3_two_one;
    tf::transformTFToMsg(ttwo, t3_two_one);
    geometry_msgs::Transform t3_one_three;
    tf::transformTFToMsg(tthree, t3_one_three);
    
    ros::Rate timer(.5);

    while(ros::ok())
    {
        timer.sleep();
        int i = 0;

        if(i%3 == 0)
        {
            trans_s_pub.publish(t3s_one_two);
            trans_pub.publish(t3_one_two);
        }
        else if(i++%3 == 1){
            trans_s_pub.publish(t3s_two_one);
            trans_pub.publish(t3_two_one);
        }
        else{
            trans_s_pub.publish(t3s_one_three);
            trans_pub.publish(t3_one_three);
        }
    }
}