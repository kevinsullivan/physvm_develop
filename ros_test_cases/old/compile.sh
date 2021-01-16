
cd affine_tests
rm -rf devel build src/CMakeLists.txt .catkin_workspace
catkin_make
source devel/setup.bash
cd ..


cd current_feature_tests
rm -rf devel build src/CMakeLists.txt .catkin_workspace
catkin_make
source devel/setup.bash
cd ..

cd initial_feature_tests
rm -rf devel build src/CMakeLists.txt .catkin_workspace
catkin_make
source devel/setup.bash
cd ..

cd ros_failure_tests
rm -rf devel build src/CMakeLists.txt .catkin_workspace
catkin_make
source devel/setup.bash
cd ..