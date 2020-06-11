

#include <vector>
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/LinearMath/Transform.h>
#include <tf/LinearMath/Vector3.h>
#include <tf/transform_datatypes.h>

#include <tf2_geometry_msgs/tf2_geometry_msgs.h>




//add, multiply, subtract, divide two vectors in different base

//add two points together

//transform vector in different base, with or without stamp?

//implement urdf file and static transform in configuration file



std::vector<geometry_msgs::Transform> trans;

std::vector<geometry_msgs::TransformStamped> trans_s;

std::vector<geometry_msgs::Vector3Stamped> vecs_s;

std::vector<geometry_msgs::Vector3> vecs;

void transformCallback(const geometry_msgs::TransformConstPtr& data){
    trans.push_back(*data);
}

void transformStampedCallback(const geometry_msgs::TransformStampedConstPtr& data){
    trans_s.push_back(*data);
}

void vecCallback(const geometry_msgs::Vector3ConstPtr& data){
    vecs.push_back(*data);

    if(vecs.size() == 2)
    {
        //first vec should be in frame one, second should be in frame two

        geometry_msgs::Vector3 new_vec;
        new_vec.x = vecs[0].x + vecs[1].x;
        new_vec.y = vecs[0].y + vecs[1].y;
        new_vec.z = vecs[0].z + vecs[1].z;
    }
    else if(trans.size() > 2 and vecs.size() > 1){
        geometry_msgs::Vector3 new_vec;
    }
}

void vecStampedCallback(const geometry_msgs::Vector3StampedConstPtr& data){
    vecs_s.push_back(*data);

    if(vecs_s.size() == 2)
    {
        geometry_msgs::Vector3Stamped new_vec;
        new_vec.vector.x = vecs_s[0].vector.x + vecs_s[1].vector.x;
        new_vec.vector.y = vecs_s[0].vector.y + vecs_s[1].vector.y;
        new_vec.vector.z = vecs_s[0].vector.z + vecs_s[1].vector.z;
        new_vec.vector.x = vecs_s[0].vector.x - vecs_s[1].vector.x;
        new_vec.vector.y = vecs_s[0].vector.y - vecs_s[1].vector.y;
        new_vec.vector.z = vecs_s[0].vector.z - vecs_s[1].vector.z;
        new_vec.vector.x = vecs_s[0].vector.x * vecs_s[1].vector.x;
        new_vec.vector.y = vecs_s[0].vector.y * vecs_s[1].vector.y;
        new_vec.vector.z = vecs_s[0].vector.z * vecs_s[1].vector.z;


    }
    else if(trans_s.size() > 2 and vecs_s.size() > 1)
    {
        geometry_msgs::Vector3Stamped new_vec;
        tf2::doTransform(vecs_s[1], new_vec, trans_s[2]);
    }
}

int main(int argc, char **argv)
{
    // Initialize the ROS node and register it with the roscore
    ros::init(argc, argv, "helloworld");
    ros::NodeHandle node;

    auto vec_sub = node.subscribe("/vecs", 25000000, vecCallback);
    auto vec_s_sub = node.subscribe("/vecs_s", 25000000, vecStampedCallback);
    auto transform_sub = node.subscribe("/trans", 25000000, transformCallback);
    auto transform_s_sub = node.subscribe("/trans_s", 25000000, transformStampedCallback);

    ros::Rate timer(1);

    while(ros::ok())
    {
        timer.sleep();
    }


    return 0;
}