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

Name -  Simple 4 Line Program
Description - This is our standard test over the past month with an extra line included.
    A very important question to consider is : should users be annotating every AST node?
    Or, for example, if a user has already annotated a variable, should that propagate to all its reference expressions?
    This has come up several times with mixed opinions.

    Should annotations be named? 
    I don't have the "Define - Interpret" mechanism implemented
Expected Outcome - 
    One world space is created. 
    Two Points are annotated in this space, and One Vector is inferred.
    The final line cannot parse due to a bug.
Implementation Gaps - 
  -Layer 1 (Parsers) : 
    Line 41 doesn't work - I have a few minor bugs parsing floats
    I cannot parse values from Clang. Clang does not natively support this, but, I did find a hack. It's 1-2 days of work to fix this.
  -Layer 2 (Peirce) :
    I potentially need to "hide" scalars in Vector literals.
    Value inference is a nonstarter so far (short of abusing parts of lean or doing static analysis in Peirce)
  -Layer 3 (Lang) :
    Vectors, Points, and Scalars are not implemented in Lang
    Frames are not implemented
  -Layer 4 (Phys) :
    Vectors and Points are not implemented in Lang
    Frames are not implemented
  -Layer 5 (CharlieLayer) :
    Frames are not implemented
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


    //6 : @@EuclideanGeometryPoint tf_start_point = EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,worldGeometry.stdFrame)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //7 : @@EuclideanGeometryPoint tf_end_point = EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>)
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    //8 (INFERRED?) : @@EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,worldGeometry.stdFrame)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;

    //9 DON'T PROVIDE AN ANNOTATION HERE - DOESN'T WORK!
    tf::Vector3 doesnt_work = tf::Vector3(20.0, -2.0, 10.0);
}