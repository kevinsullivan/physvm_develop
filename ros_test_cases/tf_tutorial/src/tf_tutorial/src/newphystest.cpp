
/*
The standard ROS/tf tutorial program.

http://wiki.ros.org/navigation/Tutorials/RobotSetup/TF

*/

#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <tf/transform_listener.h>
#include <tf/transform_broadcaster.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"


#include <cmath>

//for today's (3/9 meeting)

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);
    //Instantiate 3d Geometric space, measurement system, etc...
    //Define base link frame and left leg
    
    //Add frame-respective interpretations
    tf::Vector3 vec_in_base_link = tf::Vector3(1,1,1);
    tf::Vector3 vec_in_left_leg = tf::Vector3(1,1,1);
    //No type error here
    tf::Vector3 vec_add_okay = vec_in_base_link + vec_in_base_link;
    
    //Type error here
    tf::Vector3 vec_add_bad = vec_in_base_link + vec_in_left_leg;

    //Define nanoseconds and seconds MS

    float secs = 5;

    float nanos = 5;

    float tensecs = secs + secs;

    float problem = secs + nanos;


}