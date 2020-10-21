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
    This tests the creation of a point and vector. 
Expected Outcome - 
    One world space is created. 
    Two Points are annotated in this space, and One Vector is inferred.
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

    //7 : @@EuclideanGeometryPoint tf_start_point = EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,worldGeometry.stdFrame,si)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //8 : @@EuclideanGeometryPoint tf_end_point = EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>, si)
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    //9 (INFERRED?) : @@EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,worldGeometry.stdFrame, si)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
}