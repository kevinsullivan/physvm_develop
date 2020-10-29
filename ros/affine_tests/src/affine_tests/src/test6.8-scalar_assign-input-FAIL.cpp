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
Test 6.8 - Scalar Assignment Failure


Description - This test defines a scalar variable in a Time and
    Euclidean space and then attempts to assign one to the other,
    which results in a failure.



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
    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry(3)
    //2 : @@ClassicalTime worldTime = ClassicalTime()

    //ERRONEOUS ANNOTATION - ASSIGNMENT OF SCALAR IN DIFFERENT SPACE
    //3 : @@TimeScalar timescalar = TimeScalar(worldTime,Value=1)
    tfScalar timescalar = x;

    //4 : @@EuclideanGeometry3Scalar euclidscalar = EuclideanGeometry3Scalar(worldGeometry,<>)
    tfScalar euclidscalar;

    //ERROR
    euclidScalar = timescalar;
}