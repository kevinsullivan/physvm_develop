Issue: 
    https://github.com/cra-ros-pkg/robot_localization/pull/522

TEST 1:

Categorization: Frame Id Mismatch

File:
    robot_localization/src/ros_filter.cpp/

Line: line 2584

Commit: 1efe3a


Code:
    {
        // Otherwise, we should use our target frame
        finalTargetFrame = targetFrame;
        poseTmp.frame_id_ = (differential && !imuData ? finalTargetFrame : msg->header.frame_id);
    }
    ...
    
      tf2::fromMsg(msg->pose.pose.orientation, orientation);
      if (fabs(orientation.length() - 1.0) > 0.01)
      {
        ROS_WARN_ONCE("An input was not normalized, this should NOT happen, but will normalize.");
        orientation.normalize();
      }
    }

    // Fill out the orientation data
    poseTmp.setRotation(orientation);

Short Description: When processing pose data (potentially from an IMU), the frame id of a pose being operated upon may be incorrectly assigned during differential drive mode. When this occurs, several operations occur downstream that reflect an incorrect understanding of the actual frame id.

Error Location/Description: Several errors occur in the function, although in our test case, we can see that a pose's orientation and position, which is in the target frame, is being assigned from the IMU data, which is in the IMU frame.

Changes in Peirce: Handling Poses end-to-end, (Possibly) Control Flow, Assertions