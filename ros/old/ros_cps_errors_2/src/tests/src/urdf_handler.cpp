
//#include <urdf/model.h>   <-- THIS ISN'T AVAILABLE IN MELODIC :(
#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/LinearMath/Quaternion.h>
#include <tf/LinearMath/Transform.h>
#include <tf/LinearMath/Vector3.h>
#include <tf/transform_datatypes.h>

#include <kdl_parser/kdl_parser.hpp>
#include <robot_state_publisher/robot_state_publisher.h>


/*
*   THIS FILE IS A ROS NODE
*    IT PUBLISHES A SET OF VARIOUS TRANSFORMS TO BE CONSUMED BY HELLOWORLD WHEN TESTING
*   THESE TRANSFORMS ARE CALCULATED BASED ON THE MODEL DEFINED IN URDF FOLDER. 
    STANDARD URDF PARSER ISN'T AVAILABLE, SO HAVE TO FALL BACK ON KDL.
*/

int main(int argc, char **argv)
{
    ros::init(argc, argv, "urdf_handler");
    
    ros::NodeHandle node;
    
    ros::Rate timer(1000);

    ROS_INFO("HELP!");
    
    KDL::Tree my_tree;
    try{
        if(kdl_parser::treeFromFile("/peirce/ros/ros_cps_errors/src/tests/urdf/test.urdf", my_tree))
        {
            robot_state_publisher::RobotStatePublisher rsp = robot_state_publisher::RobotStatePublisher(my_tree);


            while(ros::ok())
            {
                timer.sleep();
                ros::Duration(2).sleep();

                rsp.publishFixedTransforms("");

            }
        }
    }
    catch(std::exception& ex){

    }
}