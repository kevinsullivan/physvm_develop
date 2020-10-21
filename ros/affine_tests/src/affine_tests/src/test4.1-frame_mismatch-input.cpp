
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
Test 4.1

Name - Derived Frame Mismatch
Description - 
    The purpose of this test is to demonstrate an error caused by subtracting two points
    that belong to different frames.
Expected Outcome - 
    Several spaces are created. An alias for a standard frame is created.
    A derived frame is created from the standard frame.
    Two points are created, respectively expressed in the standard and derived frames.
    Those points are subtracted into a vector, which triggers an error.
Implementation Gaps - 
    Same gaps as Test 4.
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) : No frame support
  -Layer 4 (Phys) : No frame support
  -Layer 5 (CharlieLayer) : Derived frames are not explicitly supported.
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
    //6 : @@ClassicalGeometryFrame robotFrame = ClassicalGeometryFrame(worldGeometry, worldGeometry.stdFrame, <origin=<1,1,1>,basis=<<1,1,1>,<1,1,1>,<1,1,1>>>)
    //7 : @@MeasurementSystem si = SI()

    //8 : @@EuclideanGeometryPoint tf_start_point = EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,stdWorldFrame,si)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //9 : @@EuclideanGeometryPoint tf_end_point = EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>,robotFrame,si)
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    //10 (Error?) : @@EuclideanGeometryVector tf_displacement = EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,worldGeometry.stdFrame,si)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;

}