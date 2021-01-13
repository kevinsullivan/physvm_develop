
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
Test 2.1 -  Standard Frame Creation


Description - This test first creates a set of Spaces, then it creates a standard basis variable
and binds an existing standard basis to it.
Expected Outcome - worldVelocity.stdFrame will be bound to a variable called stdVelFrame.
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
    
    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry(3)
    //2 : @@ClassicalTime worldTime = ClassicalTime()
    //3 : @@ClassicalVelocity3 worldVelocity = ClassicalVelocity(worldGeometry, worldTime)
    //4 : @@ClassicalVelocity3Basis stdVelBasis = worldVelocity.stdBasis

}