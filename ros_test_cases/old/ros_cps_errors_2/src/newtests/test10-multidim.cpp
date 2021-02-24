
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"

#include <cmath>

/*
Test 10

Name - Exotic Dimensional Expressions
Description - This test showcases several exotic dimensional types that are modeled in ROS and can be present in real code ( I have not collected data on these)
Expected Outcome - 
Implementation Gaps - 
  -Layer 1 (Parsers) :
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
  -Layer 5 (CharlieLayer) :
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
}