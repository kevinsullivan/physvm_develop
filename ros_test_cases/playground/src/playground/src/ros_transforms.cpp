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


int main(int argc, char **argv){
    // Initialize ROS and provide name for this Node
    ros::init(argc, argv, "transformation_tests");

    // Create ROS node (calling ros::start() when first node is created)
    ros::NodeHandle node;

    // Set ROS logging level to DEBUG 
    ros::console::set_logger_level(
                        ROSCONSOLE_DEFAULT_NAME, 
                        ros::console::levels::Debug);
    ros::console::notifyLoggerLevelsChanged();

    

    //world geom
    //bind std
    //der frame 1
    //der frame 2

    //std -> 1
    tf::Transform tran1 = tf::Transform();

    //1 -> 2
    tf::Transform tran2 = tf::Transform();

    //std -> 2
    tf::Transform tran3 = tf::Transform();

    //std -> 2
    tf::Transform tran4 = tran1 * tran2;

    //error!
    tf::Transform tran5 = tran1 * tran3;

    tf::Vector3 inp = tf::Vector3(1,1,1);

    tf::Vector3 out1 = tran1*inp;

    //error!
    tf::Vector3 out2 = tran2*inp;
}