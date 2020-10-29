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
Test 8.2 - Jerk Calculation


Description - This example details the construction of a jerk 
vector quantity. The object is constructed by dividing a displacement vector
by 3 time quantities representing instants.


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
    //3 : @@ClassicalTimeFrame stdWorldTime = worldTime.stdFrame with si
    //4 : @@EuclideanGeometry3 worldGeometry = EuclideanGeometry()
    //5 : @@EuclideanGeometry3Frame stdWorldGeometry = worldGeometry.stdFrame with si
    //6 : @@ClassicalVelocity3 worldVelocity = ClassicalVelocity()
    //7 : @@ClassicalVelocity3Basis stdWorldVelocity = worldVelocity.stdBasis with si
    //8 : @@ClassicalAcceleration3 worldAcceleration = ClassicalAcceleration()
    //9 : @@ClassicalAcceleration3Frame stdWorldAcceleration = worldAcceleration.stdBasis with si


    //8 : @@ClassicalTimePoint then = ClassicalTimePoint()
    ros::Time then = ros::Time::now();

    ros::Duration(1).sleep();

    //9 : @@ClassicalTimePoint now = ClassicalTimePoint(worldTime,<UNK>,stdWorldTime)
    ros::Time now = ros::Time::now();

    //10 : @@ClassicalTimeVector diff = ClassicalTimeVector(worldTime,<UNK>,stdWorldTime)
    ros::Duration diff = now - then;

    //11 : @@ClassicalTimeQuantity as_qt = ClassicalTimeQuantity(worldTime,<UNK>) with si
    tfScalar as_qt = diff.toSecs();

    //12 : @@EuclideanGeometry3Vector displacement = EuclideanGeometry3Vector(worldGeometry,<1,1,1>,stdWorldGeometry)
    tf::Vector3 displacement(1, 1, 1);

    //13 : @@ClassicalVelocity3Vector disp_per_second = ClassicalVelocity3Vector(worldVelocity,<UNK>,stdWorldVelocity)
    tf::Vector3 disp_per_second = displacement/as_qt;

    //14 : @@ClassicalAcceleration3Vector disp_per_second_squared = ClassicalAcceleration3Vector(worldAcceleration,<UNK>,disp_per_second_squared)
    tf::Vector3 disp_per_second_squared = disp_per_second/as_qt
}