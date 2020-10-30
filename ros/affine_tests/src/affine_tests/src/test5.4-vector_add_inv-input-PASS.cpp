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
Test 5.4 - Vector Add Inverse Test


Description - This vector defines a vector, provides it with an
  intepretation, and takes the additive inverse of the vector.


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
    //2 : @@MeasurementSystem si = SI()
    //3 : @@EuclideanGeometry3Frame stdWorldFrame = worldGeometry.stdFrame with si

    //4 : @@EuclideanGeometry3Vector tf_dir_vec = = EuclideanGeometry3Vector(worldGeometry,Value=<1,1,1>stdWorldFrame)
    tf::Vector3
        tf_dir_vec =tf::Vector3(1,1,1);

    //5 : @@EuclideanGeometry3Vector add_inv = EuclideanGeometry3Vector(worldGeometry,Value=<-1,-1,-1>stdWorldFrame)
    tf::Vector3 add_inv = -tf_dir_vec;
}