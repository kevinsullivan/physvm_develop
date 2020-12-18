
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
Test 1 - Space Creation


Description - The purpose of this test is to demonstrate the creation of various spaces
-- ClassicalTime
-- ClassicalGeometry

Expected Outcome - Two "World Spaces" will have been created
Implementation Gaps - NONE
  -Layer 1 (Parsers) :
  -Layer 2 (Peirce) :
  -Layer 3 (Lang) :
  -Layer 4 (Phys) :
  -Layer 5 (CharlieLayer) :
*/



#include <cmath>
/*
int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry3 worldGeometry =  EuclideanGeometry(3)
    //2 : @@ClassicalTime worldTime = ClassicalTime()
}
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");
    ros::NodeHandle node;  
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : worldTime = ClassicalTime()
    //2 si = SI()
    //3 : timeFrame = worldTime.stdFrame() with si
    //4 : timePoint = ClassicalTimePoint(worldTime,stdFrame,<5>)
    tf::Point geomPoint = tf::Point(1,1,1);
    
    //5 : timeVec = ClassicalTimeVector(worldTime,stdFrame,<10>)
    
    tf::Vector3 geomVec = tf::Vector3(2,2,2);
    tf::Vector3 geomVec2 = tf::Vector3(2,2,2);
    tf::Vector3 vec_sum = geomVec + geomVec2;

    tf::Point geom_add = geomPoint + geomVec;

    tf::Point this_is_bad = geomPoint + geomPoint;

    double scalar = 1;

    tf::Vector3 scaleVec = geomVec*scalar; // -> scalar*vector
    
    //ros::Time ptPlusVec = timePoint + timeVec;
    //ros::Time ptPlusPt = timePoint + timePoint;
}
///peirce/ros/affine_tests/src/affine_tests/src/test1-space_creation-input-PASS.cpp