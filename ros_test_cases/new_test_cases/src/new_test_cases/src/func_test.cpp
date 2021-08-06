#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <cmath>


tf::Vector3 func_test(){
    return tf::Vector3();
};

tf::Vector3 tst2(){
    tf::Vector3 vecvec = tf::Vector3();

    return vecvec;
};


ros::Duration arg_test(tf::Vector3 arg, ros::Time tmmmm){
    ros::Duration dur = ros::Duration(1);

    ros::Duration dur2 = ros::Duration(2) + dur;

    return dur2;
};


std::string noop(tf::Vector3 vv, ros::Time tm){
    return "";
};


int main(int argc, char **argv){
    ros::init(argc, argv, "");
    ros::NodeHandle node;

    tf::Vector3 arg = tf::Vector3(1,2,3);

    tf::Vector3 res = func_test();

    ros::Time now = ros::Time::now();

    ros::Duration res3 = arg_test(tf::Vector3(4,5,6), ros::Time::now());


}