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

/*
While trying to create a transform from the World->UTM using an intermediate frame, base link, 
the user accidentally attempts to create World->UTM by composing World->base_link with base_link_yaw_only->UTM. 
This transform happens to be valid, except on a slope where the yaw rotation varies. 
*/
int main(int argc, char **argv){
    ros::init(argc, argv, " ");
    ros::NodeHandle node;  

    /*
        HEADER FILE 

        line 300
        
        //! @brief Latest IMU orientation
        //!
        tf2::Transform transform_world_pose_;

        line 302

        //! @brief Holds the Cartesian->odom transform
        //!
        tf2::Transform cartesian_world_transform_;
    */
    /*
    line 240 ~300
    tf2::Transform transform_cartesian_pose_corrected;
      if (!use_manual_datum_)
      {
        getRobotOriginCartesianPose(transform_cartesian_pose_, transform_cartesian_pose_corrected, ros::Time(0));
      }
      else
      {
        transform_cartesian_pose_corrected = transform_cartesian_pose_;
      }

      // Get the IMU's current RPY values. Need the raw values (for yaw, anyway).
      tf2::Matrix3x3 mat(transform_orientation_);

      // Convert to RPY
      double imu_roll;
      double imu_pitch;
      double imu_yaw;
      mat.getRPY(imu_roll, imu_pitch, imu_yaw);

      // Convert to tf-friendly structures
      tf2::Quaternion imu_quat;
      imu_quat.setRPY(0.0, 0.0, imu_yaw);

      tf2::Transform cartesian_pose_with_orientation;
      cartesian_pose_with_orientation.setOrigin(transform_cartesian_pose_corrected.getOrigin());
      cartesian_pose_with_orientation.setRotation(imu_quat);

      cartesian_world_transform_.mult(transform_world_pose_, cartesian_pose_with_orientation.inverse());

    */

    //UPDATED VERSION (newer commit):
    //line 308
   // cartesian_world_transform_.mult(transform_world_pose_yaw_only, cartesian_pose_with_orientation.inverse());

   /*
    double odom_roll, odom_pitch, odom_yaw;
    tf2::Matrix3x3(transform_world_pose_.getRotation()).getRPY(odom_roll, odom_pitch, odom_yaw);
    tf2::Quaternion odom_quat;
    odom_quat.setRPY(0.0, 0.0, odom_yaw);
    tf2::Transform transform_world_pose_yaw_only(transform_world_pose_);
    transform_world_pose_yaw_only.setRotation(odom_quat);
    


    cartesian_world_transform_.mult(transform_world_pose_yaw_only, cartesian_pose_with_orientation.inverse());
   *///
    
    //Annotate a global Euclidean space, frame, measurement system
    //Declare a World frame, Base link frame, UTM frame, and a Base Link Yaw Only frame 
    //(derived from base link, with a new orientation applied)
     //
    //Annotate this as a transform from World->Base link
    tf::Transform transform_world_pose_;

    //Annotate this as a transform from World->UTM
    tf::Transform cartesian_world_transform_;

    //Annotate this as a transform from UTM->Base Link Yaw Only
    tf::Transform cartesian_pose_with_orientation;
////
    //This is an assignment, a type error should trigger automatically in Lean provided the prior annotations are given
    cartesian_world_transform_.mult(transform_world_pose_, cartesian_pose_with_orientation.inverse());

    //cartesian_world_transform = transform_world_pose_ * (COMPOSITION) cartesian_pose_with_orientation(\-1)
  //
  //

}