
#include "ros/ros.h"
#include "geometry_msgs/PointStamped.h"


/*
*   THIS FILE IS A ROS NODE
*    IT PUBLISHES A SET OF VARIOUS **POINTS** TO BE CONSUMED BY HELLOWORLD WHEN TESTING
*
*/





int main(int argc, char **argv)
{
    ros::init(argc, argv, "get_point");
    
    ros::NodeHandle node;

    auto point_stamped_pub = node.advertise<geometry_msgs::PointStamped>("/points_s", 25000000);
    auto point_pub = node.advertise<geometry_msgs::Point>("/points", 25000000);

    geometry_msgs::PointStamped ps_one;
    ps_one.header.frame_id = "map";
    ps_one.point.x = 1;
    ps_one.point.y = 1;
    ps_one.point.z = 1;

    geometry_msgs::Point p_one;
    p_one.x = ps_one.point.x;
    p_one.y = ps_one.point.y;
    p_one.z = ps_one.point.z; 

    geometry_msgs::PointStamped ps_two;
    ps_two.header.frame_id = "two";
    ps_two.point.x = 1;
    ps_two.point.y = 1;
    ps_two.point.z = 1;

    geometry_msgs::Point p_two;
    p_two.x = ps_two.point.x;
    p_two.y = ps_two.point.y;
    p_two.z = ps_two.point.z; 

    geometry_msgs::PointStamped ps_three;
    ps_three.header.frame_id = "three";
    ps_three.point.x = 1;
    ps_three.point.y = 1;
    ps_three.point.z = 1;

    geometry_msgs::Point p_three;
    p_three.x = ps_three.point.x;
    p_three.y = ps_three.point.y;
    p_three.z = ps_three.point.z; 

    ros::Rate timer(1000);

        int i = 0;
    while(ros::ok())
    {
        timer.sleep();
        ros::Duration(1).sleep();


        if(i%3 == 0){
            point_stamped_pub.publish(ps_one);
            point_pub.publish(p_one);
        }
        else if(i%3 == 1){
            point_stamped_pub.publish(ps_two);
            point_pub.publish(p_two);
        }
        else{
            point_stamped_pub.publish(ps_three);
            point_pub.publish(p_three);
        }
        i++;

    }




}