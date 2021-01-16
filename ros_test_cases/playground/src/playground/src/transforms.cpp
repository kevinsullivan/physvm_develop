
/*
This program provides examples involving the creation
and application of Tf transforms. For documentation see
http://docs.ros.org/en/kinetic/api/tf/html/c++/classtf_1_1Transform.html#details.
Briefly, "The Transform class supports rigid transforms
with only translation and rotation and no scaling/shear. 
It can be used in combination with Vector3, Quaternion and
Matrix3x3 linear algebra classes." 
*/

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


int main(int argc, char **argv){
    // Initialize ROS and provide name for this Node
    ros::init(argc, argv, "transformation_tests");

    // Create ROS node (calling ros::start() when first node is created)
    ros::NodeHandle node;

    // Set ROS logging level to DEBUG 
    ros::console::set_logger_level(
                        ROSCONSOLE_DEFAULT_NAME, 
                        ros::console::levels::Debug);
    ros::console::notifyLoggerLevelsChanged();

    /*
    Unit and coordinate conventions used in ROS:
    https://www.ros.org/reps/rep-0103.html. 
    
    It notes that "Inconsistency in units and 
    conventions is a common source of integration 
    issues for developers and can also lead to 
    software bugs."

    Ros standardizes on the SI unit system. Base
    units are meter, kilogram, second, ampere.
    Derived units are radian, hertz, newton, watt,
    volt, celsius, and tesla.

    Coordinate frame conventions vary depending
    on intended use, including (forward, left, up),
    (east, north, up), (right, down, forward) for
    camera suffix frames.

    Representations of rotations are several:
    quaternion, rotation matrix, roll/pitch/ya,
    and Euler angles (and for geograpic coords
    east is at yaw=0 increasing counter-clockise,
    which differs from the usual compass bearing 
    has north at yaw=0 and increases clockwise).

    There's more, on covariance matrix reps. See
    the documentation.
    */

    /*
    Frame conventions are documented here:
    https://www.ros.org/reps/rep-0105.html.
    "Developers of drivers, models, and libraries
    need a share convention for coordinate frames
    in order to better integrate and re-use 
    software components." An understatement!

    ROS uses a number of standardized frames.
    - base_link (per vehicle)
    - odom (per vehicle)
    - map
    - earth

    More. TBD.
    */
    
    /*
    KS: Problem: At this point in the execution of
    this program we have implicit content in the 
    form of a "world" geometric space and a world  implicit
    time space
    */

    //world geom
    //bind std
    //der frame 1
    //der frame 2

    //std -> 1
    tf::Transform tran1 = tf::Transform();

    //1 -> 2
    tf::Transform tran2 = tf::Transform();

    //std -> 2
    tf::Transform tran3 = tf::Transform();

    //std -> 2
    tf::Transform tran4 = tran1 * tran2;

    //error!
    tf::Transform tran5 = tran1 * tran3;

    tf::Vector3 inp = tf::Vector3(1,1,1);

    tf::Vector3 out1 = tran1*inp;

    //error!
    tf::Vector3 out2 = tran2*inp;
}