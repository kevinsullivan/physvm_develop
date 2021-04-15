cmake_minimum_required(VERSION 2.8.0)
project(new)

find_package(catkin REQUIRED COMPONENTS
  cmake_modules
  roscpp
  std_msgs
  tf
  tf2
  tf_conversions
  geometry_msgs
  kdl_parser
  joint_state_publisher
  robot_state_publisher
  nav_msgs
  map_server
)

catkin_package(
    INCLUDE_DIRS include
)

include_directories(
  include ${catkin_INCLUDE_DIRS}
)

add_executable(new src/time_test.cpp)
target_link_libraries(new ${catkin_LIBRARIES})

##include_directories(include ${catkin_INCLUDE_DIRS})
