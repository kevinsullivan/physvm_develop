Issue:
    https://github.com/UbiquityRobotics/fiducials/issues/204

TEST 1:

File:
    fiducials/fiducial_slam/src/map.cpp

Line: 235

Commit: 745ae6

Code:

    geometry_msgs::TransformStamped transform;

    try {
        transform = tfBuffer.lookupTransform(from, to, time);

        tf2::fromMsg(transform.transform, T);
        return true;

Short Description: 

Error Location/Description: 

Changes in Peirce: 