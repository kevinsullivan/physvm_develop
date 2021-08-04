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


int main(int argc, char **argv){

    std::string base_frame_id_("base_link");
    std::string global_frame_id("world");

    //Annotate a global time series of frames world->base link
    //Populate it with initial value with timestamp .05

    //Give msg a timestamp of .01
    geometry_msgs::PoseStamped msg;
    geometry_msgs::TransformStamped baseInMap;
    //Possibly embed an assertion that control flow continues executing rather than returning - prove a contradiction
    try{
        //Possibly create an assertion that the Transform Series has a timedstamped transform corresponding to this timestamp
        baseInMap = m_tfBuffer->lookupTransform(base_frame_id_, global_frame_id_, msg->header.stamp);
    } catch(tf2::TransformException){
        ROS_WARN("Failed to lookup transform!");
        return;
    }

    
    tf2::Transform baseInMapTf2;
    tf2::convert(baseInMap.transform, baseInMapTf2);
}