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
Test 9.1 - Pose Creation


Description - 
    This builds on the previous test by using a quaternion,
    in conjunction with a point, to construct a "Pose" object.

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
    //3 : @@EuclideanGeometry3Frame worldStdFrame = worldGeometry.stdFrame with si

    //4 : @@EuclideanGeometry3Rotation rot = EuclideanGeometry3Rotation(worldGeometry,<.5,.5,.5>,worldStdFrame)
    tf::Quaternion rot(.5,.5,.5);
    //5 : @@EuclideanGeometry3Point loc = EuclideanGeometry3Point(worldGeometry,<1,1,1>,worldStdFrame)
    tf::Vector3 loc (1,1,1);
    //6 : @@EuclideanGeometry3Pose p = EuclideanGeometry3Pose(worldGeometry,<<.5,.5,.5>,<1,1,1>>,worldStdFrame)
    tf::Pose p(rot,loc);


}