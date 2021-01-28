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
Test 5.0 -  Point and Vector Assignments


Description - This test defines a vector and a point in a Euclidean space,
  and then successfully assigns them to new variables.


Expected Outcome - 
Implementation Gaps - 
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
    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry(3)
    //2 : @@MeasurementSystem si = SI()
    //3 : @@EuclideanGeometry3Frame stdWorldFrame = worldGeometry.stdFrame with si

    //4 : @@EuclideanGeometry3Point tf_start_point = EuclideanGeometry3Point(worldGeometry,Value=<10,10,10>,stdWorldFrame)
    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    
    //5 : @@EuclideanGeometry3Vector tf_dir_vec = = EuclideanGeometry3Vector(worldGeometry,Value=<1,1,1>stdWorldFrame)
    tf::Vector3
        tf_dir_vec =tf::Vector3(1,1,1);

    //6 : @@EuclideanGeometry3Point tf_start_point_cp = tf_start_pt
    tf::Point
        tf_start_point_cp = tf_start_point;

    //7 : @@EuclideanGeometry3Vector tf_dir_vec_cp = tf_dir_vec
    tf::Vector3
        tf_dir_vec_cp = tf_dir_vec
}