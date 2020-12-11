
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/TransformStamped.h"



//add two vectors in different base

//transform vector in different base





int main(int argc, char **argv)
{
    ros::init(argc, argv, "get_vector");
    
    ros::NodeHandle node;

    auto vec_stamped_pub = node.advertise<geometry_msgs::Vector3Stamped>("/vecs_s", 25000000);
    auto vec_pub = node.advertise<geometry_msgs::Vector3>("/vecs", 25000000);

    geometry_msgs::Vector3Stamped v3s_one;
    v3s_one.header.frame_id = "map";
    v3s_one.vector.x = 1;
    v3s_one.vector.y = 1;
    v3s_one.vector.z = 1;

    geometry_msgs::Vector3 v3_one;
    v3_one.x = v3s_one.vector.x;
    v3_one.y = v3s_one.vector.y;
    v3_one.z = v3s_one.vector.z; 

    geometry_msgs::Vector3Stamped v3s_two;
    v3s_two.header.frame_id = "two";
    v3s_two.vector.x = 1;
    v3s_two.vector.y = 1;
    v3s_two.vector.z = 1;

    geometry_msgs::Vector3 v3_two;
    v3_two.x = v3s_two.vector.x;
    v3_two.y = v3s_two.vector.y;
    v3_two.z = v3s_two.vector.z; 

    geometry_msgs::Vector3Stamped v3s_three;
    v3s_three.header.frame_id = "three";
    v3s_three.vector.x = 1;
    v3s_three.vector.y = 1;
    v3s_three.vector.z = 1;

    geometry_msgs::Vector3 v3_three;
    v3_three.x = v3s_three.vector.x;
    v3_three.y = v3s_three.vector.y;
    v3_three.z = v3s_three.vector.z; 

    ros::Rate timer(.5);

    while(ros::ok())
    {
        timer.sleep();
        int i = 0;

        if(i%3 == 0){
            vec_stamped_pub.publish(v3s_one);
            vec_pub.publish(v3_one);
        }
        else if(i++%3 == 1){
            vec_stamped_pub.publish(v3s_one);
            vec_pub.publish(v3_one);
        }
        else{
            vec_stamped_pub.publish(v3s_one);
            vec_pub.publish(v3_one);
        }

    }




}