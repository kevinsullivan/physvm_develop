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

    bool b = argc > 1;
    tf::Vector3 myVec1, myVec2, aVelocityVector, aDisplacementVector;
    if(b){ 
      myVec1 = aVelocityVector;
      myVec2 = aVelocityVector;
    }else{
      myVec1 = aDisplacementVector;
      myVec2 = aDisplacementVector;
    }
    //{aVelocityVector,aVelocityVector} + {aDisplacementVector,aDisplacementVector}
    tf::Vector3 soundAddition_noProblem = myVec1 + myVec2; 

    /*
    2540-2627

    template<typename T>
  bool RosFilter<T>::preparePose(const geometry_msgs::PoseWithCovarianceStamped::ConstPtr &msg,
                                 const std::string &topicName,
                                 const std::string &targetFrame,
                                 const bool differential,
                                 const bool relative,
                                 const bool imuData,
                                 std::vector<int> &updateVector,
                                 Eigen::VectorXd &measurement,
                                 Eigen::MatrixXd &measurementCovariance)
  {
    bool retVal = false;

    RF_DEBUG("------ RosFilter::preparePose (" << topicName << ") ------\n");

    // 1. Get the measurement into a tf-friendly transform (pose) object
    tf2::Stamped<tf2::Transform> poseTmp;

    // We'll need this later for storing this measurement for differential integration
    tf2::Transform curMeasurement;

    // Handle issues where frame_id data is not filled out properly
    // @todo: verify that this is necessary still. New IMU handling may
    // have rendered this obsolete.
    std::string finalTargetFrame;
    if (targetFrame == "" && msg->header.frame_id == "")
    {
      // Blank target and message frames mean we can just
      // use our world_frame
      finalTargetFrame = worldFrameId_;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else if (targetFrame == "")
    {
      // A blank target frame means we shouldn't bother
      // transforming the data
      finalTargetFrame = msg->header.frame_id;
      poseTmp.frame_id_ = finalTargetFrame;
    }
    else
    {
      // Otherwise, we should use our target frame
      finalTargetFrame = targetFrame;
      poseTmp.frame_id_ = (differential && !imuData ? finalTargetFrame : msg->header.frame_id);
    }

    RF_DEBUG("Final target frame for " << topicName << " is " << finalTargetFrame << "\n");

    poseTmp.stamp_ = msg->header.stamp;

    // Fill out the position data
    poseTmp.setOrigin(tf2::Vector3(msg->pose.pose.position.x,
                                   msg->pose.pose.position.y,
                                   msg->pose.pose.position.z));

    tf2::Quaternion orientation;

    // Handle bad (empty) quaternions
    if (msg->pose.pose.orientation.x == 0 && msg->pose.pose.orientation.y == 0 &&
       msg->pose.pose.orientation.z == 0 && msg->pose.pose.orientation.w == 0)
    {
      orientation.setValue(0.0, 0.0, 0.0, 1.0);

      if (updateVector[StateMemberRoll] || updateVector[StateMemberPitch] || updateVector[StateMemberYaw])
      {
        std::stringstream stream;
        stream << "The " << topicName << " message contains an invalid orientation quaternion, " <<
                  "but its configuration is such that orientation data is being used. Correcting...";

        addDiagnostic(diagnostic_msgs::DiagnosticStatus::WARN,
                      topicName + "_orientation",
                      stream.str(),
                      false);
      }
    }
    else
    {
      tf2::fromMsg(msg->pose.pose.orientation, orientation);
      if (fabs(orientation.length() - 1.0) > 0.01)
      {
        ROS_WARN_ONCE("An input was not normalized, this should NOT happen, but will normalize.");
        orientation.normalize();
      }
    }

    // Fill out the orientation data
    poseTmp.setRotation(orientation);
    */

    /*
        2812
          poseTmp.mult(targetFrameTrans, poseTmp);
    */

    //Declare a global Euclidean space, frame, measurement system
    //Declare an IMU and Target frame
    //Annotate this Pose as being in the IMU frame
    geometry_msgs::PoseWithCovarianceStamped msg;
    msg.frame_id = "IMU";
    //Annotate this Pose as being in the Target frame
    tf2::Stamped<tf2::Transform> poseTmp;
    std::string finalTargetFrame = "Target";
    poseTmp.frame_id = finalTargetFrame;
    /*
    ...
    */
    //Give this tf2::Vector an interpretation as being in the IMU Frame
    //An automatically generated assertion you are attempting to assign a vector in one frame to a variable in another frame
    poseTmp.setOrigin(tf2::Vector3(msg->pose.pose.position.x,
                                   msg->pose.pose.position.y,
                                   msg->pose.pose.position.z));
    tf2::Quaternion orientation;

    tf2::fromMsg(msg->pose.pose.orientation, orientation);

    // Similar to above, the orientation is in the IMU frame, and we are attempting to assign it to an orientation in the target frame,
    // which a failed assertion will demonstrate.
    poseTmp.setRotation(orientation);

}