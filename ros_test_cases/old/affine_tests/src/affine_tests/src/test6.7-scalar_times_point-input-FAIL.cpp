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
Test 6.7 - Scalar Times Point


Description - This test first defines a Scalar and a Point
    and then attempts to multiply them together. 
    This results in a failure.



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

    //7 : @@EuclideanGeometry3Scalar x = EuclideanGeometry3Scalar(worldGeometry,Value=1)
    tfScalar x = 1;

    //16 : @@EuclideanGeometry3Point p = EuclideanGeometry3Point(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Point p = tf::Point(1, 1, 1);

    //17 ERROR!
    tf::Point stimesp = x*p;
}