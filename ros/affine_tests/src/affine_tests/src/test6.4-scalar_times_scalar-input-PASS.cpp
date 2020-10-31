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
Test 6.4 - Scalar Times Scalar


Description - This test defines two scalars and multiplies them
    together to yield another scalar.



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

    //2 : @@EuclideanGeometry3Scalar x = EuclideanGeometry3Scalar(worldGeometry,Value=1)
    //3 : @@EuclideanGeometry3Scalar y = EuclideanGeometry3Scalar(worldGeometry,Value=2)
    tfScalar x = 1, y = 2;

    //4 : @@EuclideanGeometry3Scalar stimess = EuclideanGeometry3Scalar(worldGeometry,Value=1)
    tfScalar stimess = x*y;
}