
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
Test 6

Name -  Basic If Conditions
Description - This illustrates basic if conditions. Some things to consider are how we label booleans.
    A question to consider is, following test3 - if we label points "once" 
        - we need to minimally consider changes in values after assignments
    How are we dealing with context?
Expected Outcome - 
    Several boolean expressions are annotated
Implementation Gaps - None
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

    //1 : @@EuclideanGeometry worldGeometry("worldGeometry", 3)

    tf::Point
    //2 : @@EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,worldGeometry.stdFrame)
        pt1 = tf::Point(10, 10, 10);
    tf::Point
    //3 : @@EuclideanGeometryPoint(worldGeometry,Value=<11,11,11>,worldGeometry.stdFrame)
        pt2 = tf::Point(11, 11, 11);

    //4: @@BooleanExpr(Value=True)
    if (pt1 < pt2)
    {
        
        //7 : @@EuclideanGeometryPoint(worldGeometry,Value=<21,21,21>,worldGeometry.stdFrame)
        pt1 += pt2;
        //5:@@BooleanExpr(Value=True)
        if(pt1 < pt2){
            
            //8 : @@EuclideanGeometryPoint(worldGeometry,Value=<11,11,11>,worldGeometry.stdFrame)
            pt1 = pt2;
        }
    }
    else
    {
        pt2 += pt1;
        //6:@@BooleanExpr(Value=False)
        if(pt1 < pt2)
        {
            pt2 = pt1;
        }
    }
}