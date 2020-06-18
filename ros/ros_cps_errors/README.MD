#ROS Demo

This mini-project contains a compile-able and runnable ROS project which demonstrates both physically consistent and physically inconsistent operations in ROS which are potentially of interest in our runtime monitor implementation.

## To Compile


cd /peirce/ros/ros_cps_errors
sh compile.sh 

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

The output should be something like : 
[ERROR] [1592520705.333526422]: ARG FRAME : two, TRANSFORM FRAME : one -> two, OUT FRAME one