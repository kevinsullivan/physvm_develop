Issue:
  https://github.com/AutonomyLab/libcreate/issues/36

TEST 1:

Categorization:

File:
  libcreate/src/create.cpp

Line:
  line 170

Commit: 
  Fix:20ed0b1
  Error:fd1d0a2

Code:
  
    if (fabs(dt) > util::EPS) {
      vel.x = deltaDist / dt;
      vel.y = 0.0;
      vel.yaw = deltaYaw / dt;
    } else {
      vel.x = 0.0;
      vel.y = 0.0;
      vel.yaw = 0.0;
    }


Short Description: 
  Time intervals used in estimation of velocity are not equal to the time intervals that actually occur when sampling changes in position. Thus, the resulting velocity calculation is incorrect.


Error Location/Description: 

Changes in Peirce: 