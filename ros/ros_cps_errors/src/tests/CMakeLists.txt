cmake_minimum_required(VERSION 2.8.0)
project(helloworld)

find_package(catkin REQUIRED COMPONENTS
  cmake_modules
  roscpp
  std_msgs
  tf
  tf2
  geometry_msgs
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

add_executable(tf_publisher src/tf_publisher.cpp)
target_link_libraries(tf_publisher ${catkin_LIBRARIES})


## add_dependencies(helloworld )

##include_directories(include ${catkin_INCLUDE_DIRS})
