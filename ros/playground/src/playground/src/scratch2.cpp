
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
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    ros::Time timePoint = ros::Time(5);
    //5 : timeVec = ClassicalTimeVector(worldTime,stdFrame,<10>)
    ros::Duration timeVec = ros::Duration(5);
    ros::Duration dsum = timeVec + timeVec;

    ros::Time timead = timePoint + timeVec;

    ros::Duration pretend_this_is_a_point = timeVec + timeVec;

    double scalar = 1;

    ros::Duration scaleVec = timeVec*scalar;//time.mul(float scalar) VS float scalar.multiply_by_random_ros_object(rosobject)

}