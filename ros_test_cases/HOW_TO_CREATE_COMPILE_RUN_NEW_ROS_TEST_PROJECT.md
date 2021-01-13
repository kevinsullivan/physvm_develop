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
9. copy CMakeLists and package.xml from another project into the project directory
10. Edit the package name, along with the "add_executable" and "target_link_libraries" using your source file names
11. Copy a launch directory from another project to /tf_tutorial/src/tf_tutorial, where the first tf_tutorial is the "workspace" directory and the second is the "project" or "package" directory. 
12. Edit the contents of the launch directory, here tf_tutorial.launch, to specify which nodes are to be run, here tf_tutorial and sensor_tutorial
13. To compile the project, open a terminal, cd to the workspace directory (here /peirce/tf_tutorial) then run the compile.sh script
    ```
    bash compile.sh
    ```
14. To run the nodes specified in the launch file, run 
    ```
    bash run.sh
    ```
15. Note: If you rename a project C++ file, you have to update the launch and CMakeLists.txt files.
