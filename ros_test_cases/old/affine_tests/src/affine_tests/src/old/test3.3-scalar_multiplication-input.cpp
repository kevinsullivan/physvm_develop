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
Test 3.1

Name - Measurement System Mismatch
Description - 
    Here we test out annotating a scalar.
    We test
    1. Scalar definition
    2. Scalar + Scalar
    3. Scalar - Scalar
    4. - Scalar
    5. Scalar * Scalar
    6. Scalar / Scalar
    7. Scalar * Vector
    8. Scalar * Point (FAILURE)
    9. Var Scalar : EuclideanScalar := x : TimeScalar (FAILURE)
Expected Outcome - 
Implementation Gaps - 
    Exactly the same set of implementation gaps as Test 3.
  -Layer 1 (Parsers) : 
  -Layer 2 (Peirce) : 
  -Layer 3 (Lang) : 
  -Layer 4 (Phys) : 
  -Layer 5 (CharlieLayer) : 
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

    //7 : @@EuclideanScalar x = EuclideanScalar(worldGeometry,Value=1)
    //8 : @@EuclideanScalar y = EuclideanScalar(worldGeometry,Value=2)
    tfScalar x = 1, y = 2;

    //9 : @@EuclideanScalar spluss = EuclideanScalar(worldGeometry,Value=3)
    tfScalar spluss = x + y;

    //10 : @@EuclideanScalar sminuss = EuclideanScalar(worldGeometry,Value=-1)
    tfScalar sminuss = x - y;

    //11 : @@EuclideanScalar invs = EuclideanScalar(worldGeometry,Value=-1)
    tfScalar invs = -x;

    //12 : @@EuclideanScalar stimess = EuclideanScalar(worldGeometry,Value=1)
    tfScalar stimess = x*x;

    //13 : @@EuclideanScalar sdivs = EuclideanScalar(worldGeometry,Value=1)
    tfScalar sdivs = x/x;

    //14 : @@EuclideanScalar v3 = EuclideanScalar(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Vector3 v3 = tf::Vector3(1, 1, 1);

    //15 : @@EuclideanVector stimesv = EuclideanVector(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Vector3 stimesv = x*v3;

    //16 : @@EuclideanPoint p = EuclideanPoint(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Point p = tf::Point(1, 1, 1);

    //17 ERROR!
    tf::Point stimesp = x*p;

    //ERRONEOUS ANNOTATION - ASSIGNMENT OF SCALAR IN DIFFERENT SPACE
    //@@TimeScalar timescalar = TimeScalar(worldTime,Value=1)
    tfScalar timescalar = x;
}