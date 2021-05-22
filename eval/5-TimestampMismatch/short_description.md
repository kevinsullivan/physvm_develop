Issue: https://github.com/ros-planning/moveit/pull/2418

TEST 1:

Categorization: Frame Timestamp Mismatch

File:
  moveit/moveit_ros/moveit_servo/src/pose_tracking.cpp

Line:
  line 236-241

Commit:
  f56e17

Code:
    try
    {
      geometry_msgs::TransformStamped target_to_planning_frame = transform_buffer_.lookupTransform(
          planning_frame_, target_pose_.header.frame_id, ros::Time(0), ros::Duration(0.1));
      tf2::doTransform(target_pose_, target_pose_, target_to_planning_frame);
    }
    catch (const tf2::TransformException& ex)
    {
    ...

Short Description: When looking up a transform, if there is a static transform available between two frames, it may assign a timestamp of 0 to the resulting pose, which may indicate that the transform is old, but is misleading to consumers of this pose, as it is technically using a recent (and old, concurrently) version of the transform.

Error Location/Description: I'm not certain, but around line 85, a call to "haveRecentTargetPose" may fail when it should not, as it does not differentiate between the static and dynamic pose.

Changes in Peirce: 
- We need a mechanism to differentiate versions of the frame by timestamps. This is not as simple as associating a frame with a timestamp and claiming that they are different. 
- Possibly more complex boolean expressions
- 
