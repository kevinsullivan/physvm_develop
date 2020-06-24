
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include "nav_msgs/MapMetaData.h"
#include "nav_msgs/OccupancyGrid.h"
#include "nav_msgs/GetMap.h"

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


int main(int argc, char **argv){
    //Initialize the ROS node and retrieve a handle to it
    ros::init(argc, argv, "velocity");   // "annotations" is ROS node name
    ros::NodeHandle node;                   // provides ROS utility functions
    //Allow debug messages to show up in console
    ros::console::set_logger_level(ROSCONSOLE_DEFAULT_NAME, ros::console::levels::Debug);


    /*
    Key insight: Just being in ROS brings in a whole set of intended physical interpretations.
    By explicating them at the top of this file

    @@
    We're working a 3D Euclidean space, let's call it s3. (Global.)
    Note: s3 comes with a standard frame, let's call it s3.std_frame.
    */
   ROS_INFO("Calling initROS (commented out for now");
    //initROS(); 
   // there is a 3D Euclidean world space (implicit in ROS, we make it explicit as "s3").
   // there is a standard frame, the "world frame", on this world space, NED, conventions, standards, ... 
   // we also have a concept of time, including ??? standard frame origin/ephemeric + seconds as a unit?


    /* BEGIN VELOCITY EXAMPLE */

    //@@We define two Points in TF, tf_start_point and tf_end_point. 
    //Both are initialized to be the world frame in the geometric 3d-space (namely, the standard frame of R3), 
    //which is instantiated and annotated above,
    //and given coordinates relative to this frame. 
    //The timestamp is initialized by subtracting a time Point from a time Vector (displacement, duration).
    //These live in a 1-dimensional affine time space, which has a default frame (namely, an origin) and reference units, instantiated in rosInit()
    //Both tf_start_point and _tf_end_point have units and dimensions expressed in meters^3
    //The timestamp properties of the points have units

    // @@ start_point is a geometric point with coordinates 10,10,10 relative to s3.std_frame
    // alternatively, before the preceding line we could've "defined" "world_frame" as s3.std_frame
    // then we could annotate the following point as having coordinates relative to "world_frame"
    // 
    tf::Stamped<tf::Point> 
        tf_start_point(tf::Point(10, 10, 10), ros::Time::now() + ros::Duration(-10), "world"), 
        tf_end_point(tf::Point(20, -2, 12), ros::Time::now(), "world");
    ros::Time start_time_point = ros::Time::now() + ros::Duration(-10), end_time_point = ros::Time::now();

        /*
        Let's fix ROS practice in preceding code regarding use of timestamps
        Note 1: Implicit in Stamped objects is a notion of a "frame as a function of time"
        Note 2: Real (wall) vs simulated time
        Note 3: Charlie advocates a coding style closer to the math, using point + vector rather than point - (-vector)
        */

       //Define a geometry_msgs version of the points to be used for eays printing
    geometry_msgs::PointStamped 
        start_point,
        end_point;
    //Perform a conversion from the tf data type to the geometry_msg data type to be printed later
    tf::pointStampedTFToMsg(tf_start_point, start_point);
    tf::pointStampedTFToMsg(tf_end_point, end_point);
    //Calculate the coordinate-wise vector displacement by the robot over the time horizon of its movement
    //@@ As both tf_end_point and tf_start_point are points, we conclude that tf_displacement is a Vector, indeed in the euclidean 3d-geometry space
    //although tf_displacement is coordinate-free, we annotate and infer that it is again in the world frame
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
    
    //Calculate the averaged coordinate-wise displacement per second of the robot, using the start and end time points, as well as the displacement vector
    //@@The result of this computation is a vector, again living in 3d geometric space. It, like its argument, is represented in the world frame
    //It has units and dimensions in meters^3/seconds^1
    //The computation on the right hand sign has a numerator and denominator. The numerator has annotations exactly as tf_displacement is defined above
    //The denominator contains a computation in parenthesis and a conversion. The computation in parenthesis involves subtracting a Point from a Point
    //and , as a result, produces a vector. This vector inherits the space, units, and dimensions  of its arguments: namely, the 1d-time space with dimensions and units of seconds^1
    tf::Vector3 tf_average_displacement_per_second = tf_displacement/(end_time_point - start_time_point).toSec();

    //We defined two vectors, displacement and velocity, which will store the exact same values as tf_displacement and tf_velocity.
    //@@As we will simply store the results of tf_displacement and tf_velocity into these two vectors, they will have the exact same annotations. Namely,
    //displacement and velocity both represent vectors in the 3d geometric space, with the "world" as the coordinate frame, with units and dimensions of meters^3
    geometry_msgs::Vector3 
        displacement, //= //tf2::toMsg(tf2_displacement),
        average_displacement_per_second; //= //tf2::toMsg(tf2_velocity);

    //These two commands are simply type conversions, so that we can take advantage of ROS's excellent formatting of geometry_msgs when printing 
    tf::vector3TFToMsg(tf_displacement, displacement);
    tf::vector3TFToMsg(tf_average_displacement_per_second, average_displacement_per_second);
    
    //Print off the start point, end point, displacement vector, and average_displacement_per_second vector
    ROS_INFO("Start Point : ");
    ROS_INFO_STREAM(start_point);
    ROS_INFO("End Point : ");
    ROS_INFO_STREAM(end_point);
    ROS_INFO("Coordinate-wise Distance displacement : ");
    ROS_INFO_STREAM(displacement);
    ROS_INFO("Coordinate-wise Velocity : ");
    ROS_INFO_STREAM(average_displacement_per_second);

    //Calculate the total distance displacement by the robot in meters
    //@@The result of this computation is a real scalar. It has units and dimensions as meters ^1. It lives in the 1d euclidean geometric space, 
    //whose frame hasn't been instantiated yet, but should be the standard basis of R1. 
    //The right hand side of this computation contains three multiplication operators and 2 additions, and one square root.
    //The operands to each of the multiplications are the coordinates of the displacement vector, which implies that they live in the 1d geometric space
    //in its standard frame, with units and dimensions in meters. The result of the multiplication, and the operands of the addition, 
    //are again in the 1d geometric space with the standard frame, but its units are now in meters^2. The result of the addition preserves both the space, frame, units, and dimensions
    //The final result of the square root operation preserves the 1d geometric space and frame, but yields dimensions and units of meters^1
    tf2Scalar absolute_distance = std::sqrt(displacement.x * displacement.x + displacement.y * displacement.y + displacement.z * displacement.z);

    //Calculate the total distance displacement by the robot in meters/sec
    //@@The result of this computation is a real scalar. It has units and dimensions as meters ^1/seconds^1. It lives in the 1d euclidean geometric space, 
    //whose frame hasn't been instantiated yet, but should be the standard basis of R1. 
    //The right hand side of this computation contains three multiplication operators and 2 additions, and one square root.
    //The operands to each of the multiplications are the coordinates of the displacement vector, which implies that they live in the 1d geometric space
    //in its standard frame, with units and dimensions in meters/second. The result of the multiplication, and the operands of the addition, 
    //are again in the 1d geometric space with the standard frame, but its units are now in meters^2/seconds^2. The result of the addition preserves both the space, frame, units, and dimensions
    //The final result of the square root operation preserves the 1d geometric space and frame, but yields dimensions and units of meters^1/seconds^1
   
    tf2Scalar absolute_velocity = std::sqrt(
        average_displacement_per_second.x * average_displacement_per_second.x + 
        average_displacement_per_second.y * average_displacement_per_second.y + 
        average_displacement_per_second.z * average_displacement_per_second.z);

    ROS_INFO("Total Distance in meters : %f", absolute_distance);

    //print off the absolute velocity of the 
    ROS_INFO("Velocity in meters/second : %f", absolute_velocity);

    /* END VELOCITY EXAMPLE */
}