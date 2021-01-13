#ROS Demo

This /peirce/ros folder contains 3 relevant sub-projects. 

"current_feature_tests" describes the 
small set of ROS programs that we are using to incrementally ensure end-to-end connection for in Peirce. 

"initial_feature_tests" describes the set of programs that we used to introduce ROS to the undergraduates as well as to prototype what we initially envisioned the annotations as looking like.

"ros_failure_tests" describes exploratory working in determining what physically inconsistent can be written in ROS. We may reuse this later on when Peirce is more fleshed out.

## To Compile


cd /peirce/ros
sh compile.sh 

## To Run

To run any of the 3 mini-projects,

cd %MINI_PROJECT_FOLDER%
Type sh devel/setup.bash
cd ..
sh run_%MINI_PROJECT_NAME%.sh

## To Stop

Ctrl+C

## Output

STRICTLY FOR THE "ros_failure_tests" project:
The program will continuously dump output to the console. Valid physical operations generate GREEN output. Invalid physical operations generate RED output.


## Annotation Note 6/18/20

If you want to run the annotation program, please do the compile step. Then, in the same directory

sh run_annotation_program.sh