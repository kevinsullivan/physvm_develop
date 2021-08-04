Issue:
  https://github.com/ros-planning/navigation/issues/796

TEST 1:

Categorization:

File:
  fake_localization/fake_localization.cpp

Line:
  line 247

Branch: 
  origin\melodic-devel
Commit: 
  b496f68

Code:
  geometry_msgs::TransformStamped baseInMap;
  try{
	// just get the latest
      baseInMap = m_tfBuffer->lookupTransform(base_frame_id_, global_frame_id_, msg->header.stamp);
  } catch(tf2::TransformException){
    ROS_WARN("Failed to lookup transform!");
  return;
Short Description: 
  A transform lookup fails because it's requested for a timestamp before it becomes available.

Error Location/Description: 
  The method fails 

Changes in Peirce: 
