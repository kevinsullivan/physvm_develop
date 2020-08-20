
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
Test 2

Name -  Zero Line Program For Derived Space Creation
Description - This test expands the previous by first creating respective Classical Geometry and Classical Time Spaces 
    and then using those to create a 
Expected Outcome - 
    This is an updated version of the previous test to demonstrate standard frames
    getting printed off into variables (do they need to be? probably not, but doesn't matter)
Implementation Gaps - 
  -Layer 1 (Parsers) :
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) : Missing
  -Layer 4 (Phys) : Missing
  -Layer 5 (CharlieLayer) : Missing
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry worldGeometry("worldGeometry", 3)
    //2 : @@ClassicalTime worldTime("worldTime")
    //3 : @@ClassicalVelocity worldVelocity(worldGeometry, worldTime)
}