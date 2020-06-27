
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

    @@EuclideanGeometry geometry(dimensions=3);
    @@Interpret ROS.worldFrame -> geometry.stdFrame=(origin="ScottStadium",frame(chirality=right, unit="m", x="north", y="east", z="up"));
    @@ClassicalTime time(origin=UTC-origin (1970-01-01T00:00:00Z ISO 8601), unit=second) // minutes are not constant duration in UTC!
    // there are many other time standards, e.g., mean solar time, with UTC closely tracking MST but not equal to it

    // part of this project at some point would be to provide a library of physical standards to which code can be interpreted
    
    // wall clock, timer, simulation time
    
    
    Reference for ROS: https://www.ros.org/reps/rep-0105.html

    /*
    UNIX TIME:

    It is the number of seconds that have elapsed since the Unix epoch, minus leap seconds;
    the Unix epoch is 00:00:00 UTC on 1 January 1970. Leap seconds are ignored,[4] with a leap
    second having the same Unix time as the second before it, and every day is treated as if 
    it contains exactly 86400 seconds.[2] Due to this treatment, Unix time is not a true 
    representation of UTC. 

    Thus, in the UTC time scale, the second and all smaller time units (millisecond, microsecond, 
    etc.) are of constant duration, but the minute and all larger time units (hour, day, week, 
    etc.) are of variable duration.
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
    //Both tf_start_point and _tf_end_point have units and dimensions expressed in meters
    //The timestamp properties of the points have units

    // @@ start_point is a geometric point with coordinates 10,10,10 relative to s3.std_frame
    // alternatively, before the preceding line we could've "defined" "world_frame" as s3.std_frame
    // then we could annotate the following point as having coordinates relative to "world_frame"
    // 
    /*
    A robot starts at position tf_start_point at time now-10, and ends up at tf_end_point at time now.
    Our goal is compute the average velocity of the robot between now-10 and now.
    */
   /*
    tf::Stamped<tf::Point> 
        tf_start_point(tf::Point(10, 10, 10), ros::Time::now() + ros::Duration(-10), "world"), 
        tf_end_point(tf::Point(20, -2, 12), ros::Time::now(), "world");*/
    tf::Point
        tf_start_point = tf::Point(10, 10, 10),
        tf_end_point = tf::Point(20, -2, 12);


    /*
    @@Interpret tf_start_point as POINT in geometry whose coordinates are 10,10,10 relative to geometry.stdFrame
    @@Interpret tf_end_point as POINT in geometry whose coordinates are 20,-2,12 relative to geometry.stdFrame
    */

    ros::Time start_time_point = ros::Time::now() + ros::Duration(-10), end_time_point = ros::Time::now();
   /*fix
    @@Interpret ros::Duration(-10) as VECTOR in time whose coordinates are -10 relative to time.UTC-origin
    @@Interpret ros::Time::now() as POINT in time whose coordinates are time.UNK1 relative to time.UTC-origin 
    @@Interpret ros::Time::now() + ros::Duration(-10) as POINT in time whose coordinates are time.UNK1 - 10 relative to time.UTC-origin
    @@Interpret start_time_point as POINT in time whose coordinates are time.UNK1 - 10 relative to time.UTC-origin
    @@Interpret ros::Time::now() as POINT in time whose coordinates are time.UNK2 relative to time.UTC-origin 
    @@Interpret end_time_point as POINT in time whose coordinates are time.UNK2 relative to time.UTC-origin
    */

    /*
    Sebastian: we can infer type of result of application of transform. Kevin: can probably already do this statically.
    
    <-- Pseudo ROS -->

    point p1;   // intended interp: world
    point p2;   // intended interp: world
    
    if (p1 == p2)  // statically would be ok 
        ...  
    transform t (world, f2);    // note that world and f2 are given explicitly as args to transform constructor
                                
    p1 = t(p1); // here can can infer p1 should be coordinatized in f2 frame 
    
    if (p1 == p2)  // FLAG, type error in terms of frame (unless world and f2 are the same)

    transform t2 (read-from-launch-file, thus dynamically defined)

    p2 = t2(p2);

    if (p1 == p2) // I do not know if this is ok - need to check at runtime
                  For it to be correct, p2 must be framed in f2
    */ 


    /*
        Let's fix ROS practice in preceding code regarding use of timestamps
        Note 1: Implicit in Stamped objects is a notion of a "frame as a function of time"
        Note 2: Real (wall) vs simulated time
        Note 3: Charlie advocates a coding style closer to the math, using point + vector rather than point - (-vector)
        */

       //Define a geometry_msgs version of the points to be used for eays printing
    geometry_msgs::Point 
        start_point,
        end_point;
    /*
    @@Interpret tf_start_point as POINT in geometry whose coordinates are geometry.UNK1 relative to geometry.stdFrame
    @@Interpret tf_end_point as POINT in geometry whose coordinates are geometry.UNK2 relative to geometry.stdFrame
    */

    //Perform a conversion from the tf data type to the geometry_msg data type to be printed later
    tf::pointTFToMsg(tf_start_point, start_point);
    tf::pointTFToMsg(tf_end_point, end_point);

    /*
    @@Interpret tf_start_point as POINT in geometry whose coordinates are 10,10,10 relative to geometry.stdFrame
    @@Interpret tf_end_point as POINT in geometry whose coordinates are 20,-2,12 relative to geometry.stdFrame
    @@Interpret start_point as POINT in geometry whose coordinates are 10,10,10 relative to geometry.stdFrame
    @@Interpret end_point as POINT in geometry whose coordinates are 20,-2,12 relative to geometry.stdFrame
    */

    //Calculate the coordinate-wise vector displacement by the robot over the time horizon of its movement
    //@@ As both tf_end_point and tf_start_point are points, we conclude that tf_displacement is a Vector, indeed in the euclidean 3d-geometry space
    //although tf_displacement is coordinate-free, we annotate and infer that it is again in the world frame
    tf::Vector3 tf_displacement = tf_end_point - tf_start_point;
    /*
    @@Interpret tf_end_point as POINT in geometry whose coordinates are 10,10,10 relative to geometry.stdFrame
    @@Interpret tf_start_point as POINT in geometry whose coordinates are 20,-2,12 relative to geometry.stdFrame
    @@Interpret tf_end_point - tf_start_point as VECTOR in geometry whose coordinates are -10,12,-2 relative to geometry.stdFrame
    @@Interpret tf_displacement as VECTOR in geometry whose coordinates are -10,12,-2 relative to geometry.stdFrame

    */


    //Calculate the averaged coordinate-wise displacement per second of the robot, using the start and end time points, as well as the displacement vector
    //@@The result of this computation is a vector, again living in 3d geometric space. It, like its argument, is represented in the world frame
    //It has units and dimensions in meters^3/seconds^1
    //The computation on the right hand sign has a numerator and denominator. The numerator has annotations exactly as tf_displacement is defined above
    //The denominator contains a computation in parenthesis and a conversion. The computation in parenthesis involves subtracting a Point from a Point
    //and , as a result, produces a vector. This vector inherits the space, units, and dimensions  of its arguments: namely, the 1d-time space with dimensions and units of seconds^1
    tf::Vector3 tf_average_displacement_per_second = tf_displacement/(end_time_point - start_time_point).toSec();
    /*
    @@Interpret tf_displacement as VECTOR in geometry whose coordinates are -10,12,-2 relative to geometry.stdFrame
    @@Interpret start_time_point as POINT in time whose coordinates are time.UNK1 - 10 relative to time.UTC-origin
    @@Interpret end_time_point as POINT in time whose coordinates are time.UNK2 relative to time.UTC-origin
    @@Interpret (end_time_point - start_time_point) as VECTOR in time whose coordinates are time.UNK2 - time.UNK1 - 10 relative to time.UTC-origin
    @@Interpret (end_time_point - start_time_point).toSec() as SCALAR in geometry whose coordinates are geometry.SCALAR1
    @@Interpret tf_displacement/(end_time_point - start_time_point).toSec() as VECTOR in geometry whose coordinates are geometry.UNK3 relative to geometry.stdFrame
    @@Interpret tf_average_displacement_per_second as VECTOR in geometry whose coordinates are geometry.UNK3 relative to geometry.stdFrame
    */

    //We defined two vectors, displacement and velocity, which will store the exact same values as tf_displacement and tf_velocity.
    //@@As we will simply store the results of tf_displacement and tf_velocity into these two vectors, they will have the exact same annotations. Namely,
    //displacement and velocity both represent vectors in the 3d geometric space, with the "world" as the coordinate frame, with units and dimensions of meters^3
    geometry_msgs::Vector3 
        displacement, //= //tf2::toMsg(tf2_displacement),
        average_displacement_per_second; //= //tf2::toMsg(tf2_velocity);
    /*
    @@Interpret tf_start_point as POINT in geometry whose coordinates are geometry.UNK4 relative to geometry.stdFrame
    @@Interpret tf_end_point as POINT in geometry whose coordinates are geometry.UNK5 relative to geometry.stdFrame
    */
    //These two commands are simply type conversions, so that we can take advantage of ROS's excellent formatting of geometry_msgs when printing 
    tf::vector3TFToMsg(tf_displacement, displacement);
    tf::vector3TFToMsg(tf_average_displacement_per_second, average_displacement_per_second);
    /*
    @@Interpret tf_displacement as VECTOR in geometry whose coordinates are -10,12,-2 relative to geometry.stdFrame
    @@Interpret tf_average_displacement_per_second as VECTOR in geometry whose coordinates are geometry.UNK3 relative to geometry.stdFrame
    @@Interpret displacement as VECTOR in geometry whose coordinates are -10,12,-2 relative to geometry.stdFrame
    @@Interpret average_displacement_per_second as VECTOR in geometry whose coordinates are geometry.UNK3 relative to geometry.stdFrame
    
    
    */
    
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
    /*
    The simplest example of a vector space over a field F is the field itself, equipped with its standard addition and multiplication. More generally, all n-tuples (sequences of length n)
        (a1, a2, ..., an)
    of elements of F form a vector space that is usually denoted Fn and called a coordinate space.

    I think sqrt can be well defined here or we can remove it?

    @@Interpret displacement.x as SCALAR in geometry whose coordinates are -10 
    @@Interpret displacement.x as SCALAR in geometry whose coordinates are -10 
    @@Interpret displacement.x*displacement.x as SCALAR in geometry whose coordinates are -20
    @@Interpret displacement.y as SCALAR in geometry whose coordinates are 12
    @@Interpret displacement.y as SCALAR in geometry whose coordinates are 12
    @@Interpret displacement.y*displacement.y as SCALAR in geometry whose coordinates are 24
    @@Interpret displacement.z as SCALAR in geometry whose coordinates are -2
    @@Interpret displacement.z as SCALAR in geometry whose coordinates are -2
    @@Interpret displacement.z*displacement.z as SCALAR in geometry whose coordinates are -4
    @@Interpret displacement.y*displacement.y+displacement.z*displacement.z as SCALAR in geometry whose coordinates are 148
    @@Interpret displacement.x*displacement.x+displacement.y*displacement.y+displacement.z*displacement.z whose coordinates are 248
    @@Interpret sqrt(displacement.x*displacement.x+displacement.y*displacement.y+displacement.z*displacement.z) as SCALAR in geometry whose coordinates are ~15.74
    @@Interpret absolute_distance as SCALAR in geometry whose coordinates are ~15.74
    

    */


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
    /*
    @@Interpret average_displacement_per_second.x as SCALAR in geometry whose coordinates are geometry.SCALAR2
    @@Interpret average_displacement_per_second.x as SCALAR in geometry whose coordinates are geometry.SCALAR2
    @@Interpret average_displacement_per_second.x*average_displacement_per_second.x as SCALAR in geometry whose coordinates are geometry.SCALAR2*geometry.SCALAR2
    @@Interpret average_displacement_per_second.y as SCALAR in geometry whose coordinates are geometry.SCALAR3
    @@Interpret average_displacement_per_second.y as SCALAR in geometry whose coordinates are geometry.SCALAR3
    @@Interpret average_displacement_per_second.y*average_displacement_per_second.y as SCALAR in geometry whose coordinates are geometry.SCALAR3*geometry.SCALAR3
    @@Interpret average_displacement_per_second.z as SCALAR in geometry whose coordinates are geometry.SCALAR4
    @@Interpret average_displacement_per_second.z as SCALAR in geometry whose coordinates are geometry.SCALAR4
    @@Interpret average_displacement_per_second.z*average_displacement_per_second.z as SCALAR in geometry whose coordinates are geometry.SCALAR4*geometry.SCALAR4
    @@Interpret average_displacement_per_second.y*average_displacement_per_second.y+average_displacement_per_second.z*average_displacement_per_second.z as SCALAR in geometry whose coordinates are geometry.SCALAR3*geometry.SCALAR3 + geometry.SCALAR4*geometry.SCALAR4
    @@Interpret average_displacement_per_second.x*average_displacement_per_second.x+average_displacement_per_second.y*average_displacement_per_second.y+average_displacement_per_second.z*average_displacement_per_second.z whose coordinates are geometry.SCALAR2*geometry.SCALAR2 + geometry.SCALAR3*geometry.SCALAR3 + geometry.SCALAR4*geometry.SCALAR4
    @@Interpret sqrt(average_displacement_per_second.x*average_displacement_per_second.x+average_displacement_per_second.y*average_displacement_per_second.y+average_displacement_per_second.z*average_displacement_per_second.z) as SCALAR in geometry whose coordinates are sqrt(geometry.SCALAR2*geometry.SCALAR2 + geometry.SCALAR3*geometry.SCALAR3 + geometry.SCALAR4*geometry.SCALAR4)
    @@Interpret absolute_distance as SCALAR in geometry whose coordinates are sqrt(geometry.SCALAR2*geometry.SCALAR2 + geometry.SCALAR3*geometry.SCALAR3 + geometry.SCALAR4*geometry.SCALAR4)
    
    */


    ROS_INFO("Total Distance in meters : %f", absolute_distance);

    //print off the absolute velocity of the 
    ROS_INFO("Velocity in meters/second : %f", absolute_velocity);

    /* END VELOCITY EXAMPLE */
}