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
Test 5.3 - Vector Plus Vector


Description - This tests defines two vectors, adds them together,
  and produces a vector as output.


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

    //4 : @@EuclideanGeometry3Vector tf_dir_vec1 = EuclideanGeometry3Vector(worldGeometry,Value=<1,1,1>,stdWorldFrame)
    tf::Vector3
        tf_dir_vec1 = tf::Point(10, 10, 10);
    
    //5 : @@EuclideanGeometry3Vector tf_dir_vec1 = EuclideanGeometry3Vector(worldGeometry,Value=<1,1,1>,stdWorldFrame)
    tf::Vector3
        tf_dir_vec2 =tf::Vector3(1,1,1);

    //6 : @@EuclideanGeometry3Vector tf_dir_vec_Sum = EuclideanGeometry3Vector(worldGeometry,Value=<2,2,2>,stdWorldFrame)
    tf::Vector3
        tf::dir_vec_sum = tf_dir_vec1 + tf_dir_vec2;
}