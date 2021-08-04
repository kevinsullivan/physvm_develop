Issue: https://github.com/mavlink/mavros/pull/208

TEST 1:

Categorization: Frame Orientation Mismatch

File:
  mavros/mavros/plugins/local_position.cpp

Line:
  83

Commit:
  030c4c
  (before bug:b6927c31)

Code:
    tf::Transform transform;
    transform.setOrigin(tf::Vector3(pos_ned.y, pos_ned.x, -pos_ned.z));
    transform.setRotation(uas->get_attitude_orientation());

Short Description: The author alleges that a position given in ENU should be converted to NED. However, this appears to be corrected from an NWU->NED conversion.

Error Location/Description: I don't know yet.

Changes in Peirce: 
- lang needs to be able to determine the orientation of a vector based on 