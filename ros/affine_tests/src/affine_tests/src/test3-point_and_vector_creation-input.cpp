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
    The following operations are tested:
    1. Point - Point
    2. Vector + Point 
    3. Vector + Vector
    4. -Point
    5. -Vector
    6. Point + Point (failure)
    7. Vector/Vector (failure)
    8. Point = Vector (failure)
    9. Vector = Point (failure)
Expected Outcome - 
    One world space is created. 
    Two Points are instantiated and annotated in this space, 
    and One Vector is instantiated and inferred.
    The Vector is added two a Point.
    One point is negated.
    The vector is negated.
    All of the above operations are successfully inferred and/or manually annotated.
    We attempt to add together two annotated points, which triggers an error due to an algebraic violation.
    We attempt to divide one Vector by another Vector, which triggers another error due to an algebraic violation.
    We attempt to assign a Vector to a Point variable, and a Point to a Vector variable, both of which result in a failure
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

    //7 : @@EuclideanGeometryPoint tf_start_point = EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,stdWorldFrame,si)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //8 : @@EuclideanGeometryPoint tf_end_point = EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>,stdWorldFrame, si)
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    //9 (INFERRED?) : @@EuclideanGeometryVector tf_displacement = EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,stdWorldFrame, si)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;

    //10 (INFERRED?) : @@EuclideanGeometryPoint back_again = tf_start_point
    tf::Point back_again = tf_start_point + tf_displacement;

    //11 (INFERRED?) : @@EuclideanGeometryVector twice = EuclideanGeometryVector(worldGeometry,Value=)
    tf::Vector3 twice = tf_displacement + tf_displacement;

    //12 (INFERRED?) : @@EuclideanGeometryPoint inv_point = EuclideanGeometryPoint(worldGeometry,Value=<-10,-10,-10>,stdWorldFrame,si)
    tf::Point inv_point = -tf_start_point;

    //13 (INFERRED?) : @@EuclideanGeometryVector inv_vector = EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,stdWorldFrame, si)
    tf::Vector3 inv_vector = -tf_displacement;

    //14 (FAILURE) 
    tf::Point pplusp = tf_start_point + tf_start_point;

    //15 (FAILURE)
    tf::Vector3 vdv = tf_displacement/tf_displacement;

    //16 (FAILURE)
    tf::Point peqv = tf_displacement;

    //17 (FAILURE)
    tf::Vector3 veqp = tf_start_point;
}