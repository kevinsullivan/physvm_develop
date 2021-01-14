# How to Set up a ROS Project for use in Peirce Project 

This project implements the standard ROS Tf Tutorial.  

Here are the steps by which we created it.

1. mkdir src
2. cd src
3. mkdir tf_tutorial
4. cd tf_tutorial
5. mkdir src
6. cd src
7. mkdir include
8. touch include/README.md
9. mkdir test (this is where files will go to accept manual annotation commands from a log file)
10. copy CMakeLists and package.xml from another project into the project/package directory (e.g., into playground/src/playground, where the first playground is the workspace directory) 
11. Edit the package name in CMakeLists.txt and in package.xml, along with the "add_executable" and "target_link_libraries" using your source file names
12. Copy a launch directory from another project to /tf_tutorial/src/tf_tutorial, where the first tf_tutorial is the "workspace" directory and the second is the "project" or "package" directory. 
13. Edit the contents of the launch directory, here tf_tutorial.launch, to specify which nodes are to be run, here tf_tutorial and sensor_tutorial
14. To compile the project, open a terminal, cd to the workspace directory (here /peirce/tf_tutorial) then run the compile.sh script
    ```
    bash compile.sh
    ```
15. To run the nodes specified in the launch file, run 
    ```
    bash run.sh
    ```
16. Note: If you rename a project C++ file, you have to update the launch and CMakeLists.txt files.
17. To run Peirce on a C++ file (let's say, ros_demo.cpp) in one these projects,
```shell
/peirce/bin/peirce <path_to>/ros_demo.cpp -extra-arg=-I/opt/ros/melodic/include/
``` 
Note that if you've created a log file of interactive inputs, let's say ros_demo_peirce.txt, just redirect it as the input stream, like this
```shell
/peirce/bin/peirce <path_to>/ros_demo.cpp -extra-arg=-I/opt/ros/melodic/include/ < <path_to>/inp_time.txt
```