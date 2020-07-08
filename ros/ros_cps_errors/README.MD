#ROS Demo

This mini-project contains a compile-able and runnable ROS project which demonstrates both physically consistent and physically inconsistent operations in ROS which are potentially of interest in our runtime monitor implementation.

## To Compile


cd /peirce/ros/ros_cps_errors
sh compile.sh 
source devel/setup.bash

## To Run

In the same directory,

sh run.sh

## To Stop

Ctrl+C

## Output

The program will continuously dump output to the console. Valid physical operations generate GREEN output. Invalid physical operations generate RED output.


## Annotation Note 6/18/20

If you want to run the annotation program, please do the compile step. Then, in the same directory

sh run_annotation_program.sh