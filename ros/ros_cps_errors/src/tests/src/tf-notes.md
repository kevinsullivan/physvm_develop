# Notes on tf library 

* Time
- Github link to documentation on negative time: https://github.com/ros2/rclcpp/issues/525

* Matrix3x3
- Implements a 3x3 rotation matrix; should only be given a pure orthogonal matrix without scaling; look like this isn't checked
- Matrix3x3 is a lousy name (too general) for a rotation-only matrix

* Transform
  - Supports rigid transforms with only translation and rotation and no scaling/shear (guessing that this is not checked)
  - Lousy name (too general, restricted to non-shear transformations; too vague, in that it does support affine transformations)
  - is the stated precondition sufficient? does it imply pure orthogonality?
