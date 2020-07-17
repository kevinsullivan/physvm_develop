
#include <g3log/g3log.hpp>
#include <g3log/logworker.hpp>
#include <string>

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
This example does not create a world, as in the previous example.

It simply serves to demonstrate a velocity calculation in ROS.

Normally, in a typical ROS program, we would want to use something such as an odometry or an IMU message from a sensor to retrieve velocity
, or interpolate it from acceleration estimates (or anything along those lines), but here we present a simple simulation for pedagogy and to
facilitate annotation.

We do not define or refer to an explicit world (or equivalently, map), as in the previous example. Instead, the world is implicitly defined
and referred to as "world" frame

The program
(1) Defines two points in terms of the world frame
(2) Defines two time points, one corresponding to each point
(3) Calculates the coordinate-wise displacement (vector) in R3, end - start
(4) Calculates the coordinate-wise average velocity in R3, end - start / end time - start time
(5) Calculates the total distance displacement and corresponding average velocity
*/

/*

Key insights from today:
- standard "global" intepretation possible for most/many ROS programs
- annotations really add definitions to an "environment" of named physical domain objects

*/

/*

@@EuclideanGeometry geom3d<3,"worldGeometry">;  // a space (affine space)
  @@ClassicalTime time<"worldTime">;              // a space (affine space)
  @@ClassicalVelocity vel<"worldVelocities">      // a space (a vector space)

  @@AffineFrame base_link_frame_(geom3d, <computed>, geom3.stdFrame);


  // geom3d.pointTorsor
  // geom3d.vectorSpace
  // geom3d.stdFrame (!)
  // geom3d.vectorSpace.stdBasis
  // vel.stdBasis

  // 1. Add a domain point objects
  // 2. Interpret geom_start as mapping to this new domain point object
  // underscores after name identify domain objects vs machine objects
  @@GeometricPoint geom_start_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
  Point3 geom_start(0.0,0.0,0.0);
  @@Interpret geom_start -> geom_start_

  @@GeometricPoint geom_end_(geom3, [0.0,0.0,0.0], geom3.stdFrame)
  Point3 geom_end(1.0,1.0,1.0);
  @@Interpret geom_end -> geom_end_

 
  @@TimePoint time_then_(time, [-10.0], time.stdFrame);
  Point1 time_then_(time, [-10.0])
  @@Intepret time_then_ -> time_then_
  
  @@TimePoint time_now_(time, [0.0], time.stdFrame);
  Point1 time_now(0.0);
  @@Intepret time_now_ -> time_now_

  @@GeometricVector geom_displacement_(geom3, [1.0,1.0,1.0], geom3.stdFrame);
  Vector3 geom_displacement = geom_end - geom_start;
  @@Interpret geom_displacement -> geom_displacement_

  @@TimeVector....
  Vector1 time_displacement = time_now - time_then;

  @@Scalar+Units ... what's going on here exactly with respect to frames?
  Scalar(?) duration = time_displacement.magnitude();

  @@VelocityVector(vel, [<computed>], <coordinate-free>)
  Vector3 displacement_per_time = geom_displacement / duration;

  Vector3 foobar = displacement_per_time + geom_displacement; // 

*/


int main(int argc, char **argv){
    //Initialize the ROS node a
using namespace g3;auto worker = g3::LogWorker::createLogWorker();std::string logFile = "Peirce.log";std::string logDir = ".";auto defaultHandler = worker->addDefaultLogger(logFile, logDir);g3::initializeLogging(worker.get());
nd retrieve a handle to it
    ros::init(argc, argv, "velocity");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);

    tf::Point
        tf_start_point = tf::Point(10, 10, 10);
    tf::Point
        tf_end_point = tf::Point(20, -2, 12);

    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
}