
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
Test 1

Name -  Simple Velocity Example
Description - This is a streamlined version of our canonical velocity program from ~6 weeks ago.
Expected Outcome - Two "World Spaces" will have been created
Implementation Gaps - 
  -Layer 1 (Parsers) :
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
  -Layer 5 (CharlieLayer) :
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    tf::Point
        tf_start_point = tf::Point(10, 10, 10),
        tf_end_point = tf::Point(20, -2, 12);
    
    ros::Time 
        start_time_point = ros::Time::now() + ros::Duration(-10), 
        end_time_point = ros::Time::now();
    
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
    
    tfScalar scalar = (end_time_point - start_time_point).toSec();

    tf::Vector3 tf_average_displacement_per_second = tf_displacement/scalar;
    

    /* END VELOCITY EXAMPLE */
}