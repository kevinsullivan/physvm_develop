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
Test 7.0 - Quantity Creation


Description - This tests the creation of a physical quantity in a time space.


Expected Outcome - 
Implementation Gaps - 
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
    Vectors and Points are not implemented in Lang
  -Layer 5 (CharlieLayer) :
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    // GIVEN
    //1 : @@ClassicalTime worldTime = ClassicalTime()
    //2 : @@MeasurementSystem si = SI()
    //3 : @@ClassicalTimeFrame stdWorldTime = worldTime.stdFrame as si

    //4 : @@ClassicalTimePoint then = ClassicalTimePoint()
    ros::Time then = ros::Time::now();

    ros::Duration(1).sleep();

    //5 : @@ClassicalTimePoint now = ClassicalTimePoint(worldTime,<UNK>,stdWorldTime)
    ros::Time now = ros::Time::now();

    //6 : @@ClassicalTimeVector diff = ClassicalTimeVector(worldTime,<UNK>,stdWorldTime)
    ros::Duration diff = now - then;

    //7 : @@ClassicalTimeQuantity as_qt = ClassicalTimeQuantity(worldTime,<UNK>) with si
    tfScalar as_qt = diff.toSecs();
}