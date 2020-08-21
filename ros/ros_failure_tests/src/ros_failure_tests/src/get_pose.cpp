
#include "ros/ros.h"
#include "geometry_msgs/PoseStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/transform_datatypes.h>



/*
*   THIS FILE IS A ROS NODE
*    IT PUBLISHES A SET OF VARIOUS **POSES** TO BE CONSUMED BY HELLOWORLD WHEN TESTING
*
*/


int main(int argc, char **argv)
{
    ros::init(argc, argv, "get_pose");
    
    ros::NodeHandle node;

    auto pose_stamped_pub = node.advertise<geometry_msgs::PoseStamped>("/pose_s", 25000000);
    auto pose_pub = node.advertise<geometry_msgs::Pose>("/poses", 25000000);
    
    tf::Quaternion tqone;
    tqone.setRPY(-1.5, 0, 1.5);
    tf::Quaternion tqtwo;
    tqtwo.setRPY(0,-1.5,1.5);
    tf::Quaternion tqthree;
    tqthree.setRPY(1.5, -1.5, 0);
    geometry_msgs::Quaternion qone, qtwo, qthree;
    tf::quaternionTFToMsg(tqone, qone);
    tf::quaternionTFToMsg(tqtwo, qtwo);
    tf::quaternionTFToMsg(tqthree, qthree);

    geometry_msgs::PoseStamped ps_one;
    ps_one.header.frame_id = "map";
    ps_one.pose.position.x = 1;
    ps_one.pose.position.y = 1;
    ps_one.pose.position.z = 1;
    ps_one.pose.orientation = qone;

    geometry_msgs::Pose p_one;
    p_one.position = ps_one.pose.position;
    p_one.orientation = ps_one.pose.orientation;

    geometry_msgs::PoseStamped ps_two;
    ps_two.header.frame_id = "two";
    ps_two.pose.position.x = 1;
    ps_two.pose.position.y = 1;
    ps_two.pose.position.z = 1;
    ps_two.pose.orientation = qtwo;

    geometry_msgs::Pose p_two;
    p_two.position = ps_two.pose.position;
    p_two.orientation = ps_two.pose.orientation;

    geometry_msgs::PoseStamped ps_three;
    ps_three.header.frame_id = "three";
    ps_three.pose.position.x = 1;
    ps_three.pose.position.y = 1;
    ps_three.pose.position.z = 1;
    ps_three.pose.orientation = qthree;

    geometry_msgs::Pose p_three;
    p_three.position = ps_three.pose.position;
    p_three.orientation = ps_three.pose.orientation;

    ros::Rate timer(1000);

        int i = 0;
    while(ros::ok())
    {
        timer.sleep();
        ros::Duration(1).sleep();


        if(i%3 == 0){
            pose_stamped_pub.publish(ps_one);
            pose_pub.publish(p_one);
        }
        else if(i%3 == 1){
            pose_stamped_pub.publish(ps_two);
            pose_pub.publish(p_two);
        }
        else{
            pose_stamped_pub.publish(ps_three);
            pose_pub.publish(p_three);
        }
        i++;

    }




}