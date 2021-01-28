
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
Test 1

Name -  Simple Velocity Example
Description - 
    We have conversions missing in Lang.
    A good question is what we're actually expecting to infer.
    Where we can't infer, annotations need to be placed as indicated.
Expected Outcome - Two "World Spaces" will have been created
Implementation Gaps - 
  -Layer 1 (Parsers) :
    I haven't implemented ros::Time. Extremely minor
  -Layer 2 (Peirce) :
    None
  -Layer 3 (Lang) :
    Derived conversions not implemented : (end_time_point - start_time_point).toSec()
  -Layer 4 (Phys) :
  -Layer 5 (CharlieLayer) :
*/

int main(int argc, char **argv){
    ros::init(argc, argv, "velocity");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    //1 : @@EuclideanGeometry worldGeometry("worldGeometry", 3)
    //2 : @@ClassicalTime worldTime("worldTime")
    //3 : @@ClassicalVelocity worldVelocity(worldGeometry, worldTime)

    tf::Point
    //4 : @@EuclideanGeometryPoint(worldGeometry,Value=<10,10,10>,worldGeometry.stdFrame)
        tf_start_point = tf::Point(10, 10, 10),
    //5 : @@EuclideanGeometryPoint(worldGeometry,Value=<20,-2,12>,worldGeometry.stdFrame)
        tf_end_point = tf::Point(20, -2, 12);
    
    
    ros::Time 
    //6 : @@ClassicalTimePoint(worldTime,Value=<UNK>,worldTime.stdFrame)
        start_time_point = ros::Time::now() + ros::Duration(-10), 
    //7 : @@ClassicalTimePoint(worldTime,Value=<UNK>,worldTime.stdFrame)
        end_time_point = ros::Time::now();
    
    //8 (INFERRED?) : @@EuclideanGeometryVector(worldGeometry,Value=<-10,12,-2>,worldGeometry.stdFrame)
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
    
    //9 (INFERRED?) : @@ClassicalTimeScalar(worldTime,Value=<UNK>)
    tfScalar scalar = (end_time_point - start_time_point).toSec();

    //10 (INFERRED?) : @@ClassicalVelocityVector(worldVelocity,Value=<UNK>,worldVelocity.stdFrame)
    tf::Vector3 tf_average_displacement_per_second = tf_displacement/scalar;
    

    /* END VELOCITY EXAMPLE */
}