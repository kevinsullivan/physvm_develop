#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
//#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <cmath>


int main(int argc, char **argv){
    ros::init(argc, argv, "new lang tests");
    ros::NodeHandle node;

    //Define Seconds Standard Space "centered at now", and Years Derived Space also "centered at now"

    //declare transform FROM seconds TO years
    float seconds_to_years = .001;
    
    //vector
    float five_seconds = 5;
    //transform duration vector to be expressed in years from seconds
    float five_secs_in_years = seconds_to_years*five_seconds;
    
    //declare time point
    float five_seconds_in_future = 5;
    //transform time point to be expressed in years from seconds
    float partial_year_in_future = seconds_to_years*five_seconds_in_future;

    //error - trying to transform a time in years but transform has domain in seconds
    float what_in_what = seconds_to_years*partial_year_in_future;

    //declare scalar
    float scalar_five = 5;
    //scale duration vector
    float seconds25 = scalar_five*five_seconds;
    //error - we don't scale points
    float time25 = scalar_five*five_seconds_in_future;

}