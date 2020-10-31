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
Test 3

Name -  Point and Vector Tests
Description - 
    This is a friendly reminder that a velocity vector in ROS will be
    expressed in a frame, not a basis.
Expected Outcome - 
    A velocity vector is defined in terms of the world frame.
    We attach it to a vector space, along with a basis, ignoring its inherent frame structure
    The interpretation does not match the real world meaning.
Implementation Gaps - 
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) :
    Missing the concept of a measurement system annotation.
  -Layer 3 (Lang) :
    Vectors, Points, and Scalars are not implemented in Lang
  -Layer 4 (Phys) :
    Vectors and Points are not implemented in Lang
  -Layer 5 (CharlieLayer) :
    Vectors and Points need to be connected to API
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    // GIVEN
    //1 : @@EuclideanGeometry worldGeometry =  EuclideanGeometryLiteral(3)
    //2 : @@ClassicalTime worldTime = ClassicalTimeLiteral()
    //3 : @@ClassicalVelocity worldVelocity = ClassicalVelocityLiteral(worldGeometry, worldTime)
    //4 : @@ClassicalAcceleration worldAcceleration = ClassicalAccelerationLiteral(worldGeometry, worldTime)
    //5 : @@ClassicalGeometryFrame stdWorldFrame = worldGeometry.stdFrame
    //6 : @@MeasurementSystem si = SI()
    //7 : @@ClassicalVelocityFrame stdVelFrame = worldVelocity.stdBasis

    //No error - interpretation does not correspond to real world meaning
    //8 : @@ClassicalVelocityVector flyVelocityInWorld = ClassicalVelocityVector(worldVelocity, Value=<1,1,1>, stdVelFrame)
    tf::Stamped<tf::Vector3> flyVelocityInWorld = 
        tf::Stamped<tf::Vector3>(tf::Vector3(1,1,1), ros::Time::now(), "world");
}