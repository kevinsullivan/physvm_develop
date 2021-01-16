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
Test 6.6 - Scalar Times Vector


Description - This test defines a scalar and a vector, and 
    then multiplies them by each other to define a new vector.



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
    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry3Geometry(3)

    //7 : @@EuclideanGeometry3Scalar x = EuclideanGeometry3Scalar(worldGeometry,Value=1)
    tfScalar x = 1;

    //14 : @@EuclideanGeometry3Scalar v3 = EuclideanGeometry3Scalar(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Vector3 v3 = tf::Vector3(1, 1, 1);

    //15 : @@EuclideanGeometry3Vector stimesv = EuclideanGeometry3Vector(worldGeometry,Value=<1,1,1>,stdWorldFrame,si)
    tf::Vector3 stimesv = x*v3;
}