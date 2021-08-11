#include "ros/ros.h"
#include "geometry_msgs/Vector3Stamped.h"
#include "geometry_msgs/Vector3.h"
#include "geometry_msgs/Transform.h"
#include "geometry_msgs/TransformStamped.h"
#include <tf/transform_datatypes.h>
#include <tf2_geometry_msgs/tf2_geometry_msgs.h>
#include <tf/transform_listener.h>
#include <tf/transform_broadcaster.h>
//#include "nav_msgs/MapMetaData.h"
//#include "nav_msgs/OccupancyGrid.h"
//#include "nav_msgs/GetMap.h"


#include <cmath>

#include <chrono>

ros::Time getHardwareTime(){
    auto curtime = std::chrono::system_clock::now();
    float timecoord = std::chrono::duration_cast<std::chrono::seconds>(curtime.duration);
    return ros::Time(timecoord,0);
}

ros::Time getSystemTime(){
    return ros::Time::now();
}



int main(int argc, char **argv){
    ros::Time hardware_clock_time = getHardwareTime();//Time in hardware space

    geometry_msgs::PoseStamped msg;//Timestamped IMU message using hardware time

    msg.header.stamp = hardware_clock_time;//Fine assignment

    ros::Time _ros_time_base = getSystemTime();//Offset In System time
    ros::Time ros_time_base_alias = _ros_time_base;//Time in System Coordinate Space
    double ros_time_base_coord = ros_time_base_alias.toSec();
    //Coordinate of a Time After Unit Transformation From System CS to a Space With Seconds as a Unit
    //Should we interpret the physical type of ros_time_base_coord (i.e., the result of calling toSec)
    //as being a Vector in the System-Seconds CS or as being the Coordinate 
    //      (of a Time Point or a Duration) in the System-Seconds CS
    /*Let's assume this is a Coordinate of a Duration 
        in a Time (dimension) Space in the System-Seconds CS
    When annotating a Coordinate extracted from a Point or a Vector
    in a physical space, do we need to keep type information
    conveying that it originated from a Point or a Vector originally?
    Assume that we do not for the time being

    1. Mapping from Point to Vector (Time to Duration)
    2. Transform to new Coordinate Space (System CS to System-Seconds CS)
    3. Extraction of a Coordinate (from Vector in SysSecCS to Coordinate SysSecCS)

    How do you formalize the actual mathematics vs. how do you expect a lay-annotator to...
    
    */
    ros::Time msg_stamp_alias = 
    double msg_coord = msg.header.stamp.toSec();

    double stamp_added_bias = ros_time_base_coord + msg_coord

    msg.header.stamp = ros::Time(stamp_added_bias);//Error occurs here - invalid assignment

}