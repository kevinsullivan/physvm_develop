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
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    /*
    355-385
    if (!odomFrame.empty()) {
        outFrame = odomFrame;
        tf2::Transform odomTransform;
        if (lookupTransform(odomFrame, baseFrame, outPose.stamp_, odomTransform)) {
            outPose.setData(basePose * odomTransform.inverse());
            outFrame = odomFrame;

            tf2::Vector3 c = odomTransform.getOrigin();
            ROS_INFO("odom   %lf %lf %lf", c.x(), c.y(), c.z());
        }
    }

    // Make outgoing transform make sense - ie only consist of x, y, yaw
    // This can be disabled via the publish_6dof_pose param, mainly for debugging
    if (!publish_6dof_pose) {
        tf2::Vector3 translation = outPose.transform.getOrigin();
        translation.setZ(0);
        outPose.transform.setOrigin(translation);
        double roll, pitch, yaw;
        outPose.transform.getBasis().getRPY(roll, pitch, yaw);
        outPose.transform.getBasis().setRPY(0, 0, yaw);
    }

    poseTf = toMsg(outPose);
    poseTf.child_frame_id = outFrame;
    havePose = true;

    if (publishPoseTf) {
        publishTf();
    }

    */
    
    geometry_msgs::TransformStamped poseTf;
    tf2::Stamped<TransformWithVariance> outPose;// = basePose;
    tf2::Stamped<TransformWithVariance> basePose;
    std::string odomFrame;
    std::string outFrame;
    std::string baseFrame;


    
    if (!odomFrame.empty()) {
        outFrame = odomFrame;
        tf2::Transform odomTransform;
        if (lookupTransform(odomFrame, baseFrame, outPose.stamp_, odomTransform)) {
            outPose.setData(basePose * odomTransform.inverse());
            outFrame = odomFrame;

            tf2::Vector3 c = odomTransform.getOrigin();
            ROS_INFO("odom   %lf %lf %lf", c.x(), c.y(), c.z());
        }
    }

    
    poseTf = toMsg(outPose);

}