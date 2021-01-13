
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
Test 4.3 - Derived Basis Creation


Description - 
    This test builds a Vector Space, takes its standard basis,
    and uses it to construct a derived basis.

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
    //2 : @@ClassicalTime worldTime = ClassicalTime()
    //3 : @@ClassicalVelocity3 worldVelocity = ClassicalVelocity(worldGeometry, worldTime)
    //4 : @@MeasurementSystem si = SI()
    //5 : @@ClassicalVelocity3Basis stdVelBasis = worldVelocity.stdBasis with SI
    
    //6 : @@ClassicalVelocity3Basis robotVel = ClassicalVelocityBasis(worldVel, stdVelBasis, <basis=<<1,1,1>,<1,1,1>,<1,1,1>>>)

    
}