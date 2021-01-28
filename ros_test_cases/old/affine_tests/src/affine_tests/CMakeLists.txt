cmake_minimum_required(VERSION 2.8.0)
project(current_feature_tests)

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

add_executable(test1_space_creation src/test1-space_creation-input.cpp)
target_link_libraries(test1_space_creation ${catkin_LIBRARIES})

add_executable(test2-standard_frame_creation src/test2-standard_frame_creation-input.cpp)
target_link_libraries(test2-standard_frame_creation ${catkin_LIBRARIES})

add_executable(test3-point_and_vector_creation src/test3-point_and_vector_creation-input.cpp)
target_link_libraries(test3-point_and_vector_creation ${catkin_LIBRARIES})

add_executable(test3.1-point_and_vector_measurement_error src/test3.1-point_and_vector_measurement_error-input.cpp)
target_link_libraries(test3.1-point_and_vector_measurement_error ${catkin_LIBRARIES})

add_executable(test4-derived_frame_creation src/test4-derived_frame_creation-input.cpp)
target_link_libraries(test4-derived_frame_creation ${catkin_LIBRARIES})

add_executable(test4.1-frame_mismatch src/test4.1-frame_mismatch-input.cpp)
target_link_libraries(test4.1-frame_mismatch ${catkin_LIBRARIES})

add_executable(test4.2-frame_match src/test4.2-frame_match-input.cpp)
target_link_libraries(test4.2-frame_match ${catkin_LIBRARIES})

add_executable(test5-transformation src/test5-transformation-input.cpp)
target_link_libraries(test5-transformation ${catkin_LIBRARIES})

add_executable(test5.1-transformation_composition_success src/test5.1-transform_composition_success-input.cpp)
target_link_libraries(test5.1-transformation_composition_success ${catkin_LIBRARIES})

add_executable(test5.2-transform_composition_error src/test5.2-transform_composition_error-input.cpp)
target_link_libraries(test5.2-transform_composition_error ${catkin_LIBRARIES})

##include_directories(include ${catkin_INCLUDE_DIRS})
