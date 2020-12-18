cmake_minimum_required(VERSION 2.8.0)
project(playground)

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

add_executable(scratch1 src/scratch1.cpp)
target_link_libraries(scratch1 ${catkin_LIBRARIES})

add_executable(scratch2 src/scratch2.cpp)
target_link_libraries(scratch2 ${catkin_LIBRARIES})

add_executable(scratch3 src/scratch3.cpp)
target_link_libraries(scratch3 ${catkin_LIBRARIES})

add_executable(scratch4 src/scratch4.cpp)
target_link_libraries(scratch4 ${catkin_LIBRARIES})

add_executable(scratch5 src/scratch5.cpp)
target_link_libraries(scratch5 ${catkin_LIBRARIES})


##include_directories(include ${catkin_INCLUDE_DIRS})
