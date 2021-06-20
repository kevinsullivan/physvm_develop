#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <cmath>


int main(int argc, char **argv){
    ros::init(argc, argv, "new lang tests");
    ros::NodeHandle node;

    tf::Vector3 vec1(3, 3, 3);
    tf::Vector3 vec2(2, 2, 2);

    tf::Vector3 vec3 = vec1 + vec2;

    tf::Vector3 vec4 = 4*vec1;

    geometry_msgs::Vector3 vec5;

    tf::Transform t1;

    tf::Transform t2;

    tf::Transform t3 = t1*t2;

    tf::Vector3 v6 = t1*vec1;
}