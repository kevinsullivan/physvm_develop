# How to run Peirce on a ROS test project.

1. Complete the Onboarding tutorial, found in ONBOARD.md
2. Make sure your VS Code is conntected to the docker container
3. Open up a terminal window
4. To run on an input file, issue the comand 
```shell
/peirce/bin/peirce /peirce/ros/affine_tests/src/affine_tests/src/test1-space_creation-input-PASS.cpp -extra-arg=-I/opt/ros/melodic/include/ < /peirce/src/inp_time.txt
```
This will run peirce for a given set of test inputs, and generate a specific output file. '/peirce/src/peirce' is the application we are running. '/peirce/ros/affine_tests/src/affine_tests/src/test1-space_creation-input-PASS.cpp' is the input file. '/peirce/src/inp_time.txt' is the list of commands.
5. To run peirce without a set of pre-determined inputs to generate a specific output file, you can issue the command
```shell
/peirce/src/peirce /peirce/ros/affine_tests/src/affine_tests/src/test1-space_creation-input-PASS.cpp -extra-arg=-I/opt/ros/melodic/include/
```
Note: The second argument (the input file) is configurable. We can replace it with any test file that Peirce is configured to handle.
6. You should be running now, and will be able to give annotations to all of the variables.
7. Right now, we have support for annotating the following:
	1. Time and 3D geometric spaces
	2. Measurement systems
	3. Derived frames, as well as binding the standard frame to a variable
	4. Points and Vectors with appropriate operations on them
	5. Preliminary support for transformations

## Annotating Variables

The important thing here is that each variable in the variable table printed requires an annotation. Each annotation requires a space, a frame, and a measurement system, so those must be created before annotating the variables.