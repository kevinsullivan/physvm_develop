
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

/*
Test 1

Test case := pair <input, expected-output>
Input := <program, annotations>
Output := physlang object

Name -  Zero Line Program For Space Creation
Description - The purpose of this test is to demonstrate the creation of ClassicalTime and ClassicalGeometry Spaces.
Expected Outcome - Two "World Spaces" will have been created
Implementation Gaps - NONE
  -Layer 1 (Parsers) :
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
  -Layer 5 (CharlieLayer) :
*/


// Input 
#include <cmath>

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry wg = worldGeometry("worldGeometry", 3)
    //2 : @@ClassicalTime wt = worldTime("worldTime")
    //3 : @@ClassicalVelocity wv = worldVelocity(worldGeometry, worldTime)
}

// Output physlang object.