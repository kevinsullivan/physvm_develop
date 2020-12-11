cmake_minimum_required(VERSION 2.8.0)
project(annotations)

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

add_executable(relative_frames src/annotate1-relative_frames.cpp)
target_link_libraries(relative_frames ${catkin_LIBRARIES})

add_executable(velocity src/annotate2-velocity.cpp)
target_link_libraries(velocity ${catkin_LIBRARIES})


##include_directories(include ${catkin_INCLUDE_DIRS})
