cmake_minimum_required(VERSION 2.8.0)
project(helloworld)

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
)

catkin_package(
    INCLUDE_DIRS include
)

include_directories(
  include ${catkin_INCLUDE_DIRS}
)

add_executable(helloworld src/helloworld.cpp)
target_link_libraries(helloworld ${catkin_LIBRARIES})

add_executable(get_vector src/get_vector.cpp)
target_link_libraries(get_vector ${catkin_LIBRARIES})

add_executable(get_pose src/get_pose.cpp)
target_link_libraries(get_pose ${catkin_LIBRARIES})

add_executable(get_point src/get_point.cpp)
target_link_libraries(get_point ${catkin_LIBRARIES})

add_executable(tf_publisher src/tf_publisher.cpp)
target_link_libraries(tf_publisher ${catkin_LIBRARIES})

add_executable(tf_broadcaster src/tf_broadcaster.cpp)
target_link_libraries(tf_broadcaster ${catkin_LIBRARIES})

add_executable(urdf_handler src/urdf_handler.cpp)
target_link_libraries(urdf_handler ${catkin_LIBRARIES})

add_executable(cases src/cases.cpp)
target_link_libraries(cases ${catkin_LIBRARIES})

## add_dependencies(helloworld )

##include_directories(include ${catkin_INCLUDE_DIRS})
