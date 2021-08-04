cd /peirce/ros_test_cases/eval

cd 1-TimestampUnitMismatches
mkdir project
cd project 
git clone https://github.com/ros2/geometry2/
cd geometry2
git checkout 2800f8

cd ..
cd ..
cd ..

cd 2-FrameIdMismatch
mkdir project
cd project 
git clone https://github.com/cra-ros-pkg/robot_localization
cd robot_localization
git checkout 1efe3a

cd ..
cd ..
cd ..


cd 3-UninitializedTransformException
mkdir project
cd project 
git clone https://github.com/ros-perception/ar_track_alvar
cd ar_track_alvar
git checkout ebb782

cd ..
cd ..
cd ..


cd 4-YawOnlyCompositionMismatch
mkdir project
cd project 
git clone https://github.com/cra-ros-pkg/robot_localization
cd robot_localization
git checkout 9277d9

cd ..
cd ..
cd ..


cd 5-TimestampMismatch
mkdir project
cd project 
git clone https://github.com/ros-planning/moveit
cd moveit 
git checkout f56e17

cd ..
cd ..
cd ..

cd 6-FrameOrientation
mkdir project 
cd project
git clone https://github.com/mavlink/mavros
cd mavros
git checkout 030c4c

cd ..
cd ..
cd ..

cd 7-InvalidFrame
mkdir project
cd project
git clone https://github.com/locusrobotics/fuse/
cd fuse
git checkout 8c3738

cd ..
cd ..
cd ..

cd 9-UnavailableTransform
mkdir project
cd project
git clone https://github.com/ros-planning/navigation/
cd fuse
git checkout b496f68

cd ..
cd ..
cd ..

cd 11-TimeSpaceMismatch
mkdir project
cd project
git clone https://github.com/IntelRealSense/realsense-ros/
cd fuse
git checkout f23fd1d

cd ..
cd ..
cd ..

cd 12-VelocityMiscalculation
mkdir project
cd project
git clone https://github.com/AutonomyLab/libcreate/
cd fuse
git checkout fd1d0a2

cd ..
cd ..
cd ..