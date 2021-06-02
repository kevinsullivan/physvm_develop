Issue:
      https://github.com/ros2/geometry2/pull/16

TEST 1:

Categorization: Invalid Transform Composition

File:
      robot_localization/src/navsat_transform.cpp
Line: 308

Commit: 9277d9

Code: 
      cartesian_world_transform_.mult(transform_world_pose_yaw_only, cartesian_pose_with_orientation.inverse());

Short Description: While trying to create a transform from the World->UTM using an intermediate frame, base link, the user accidentally attempts to create World->UTM by composing World->base_link with base_link_yaw_only->UTM. This transform happens to be valid, except on a slope where the yaw rotation varies. 

Error Location/Description: The error occurs later in execution. I cannot pinpoint an exact location where the incorrect transform is used, but it does get broadcasted on line 323, so presumably any user consuming this transform will have an error state.

Changes in Peirce: There are potentially no changes required in Peirce.