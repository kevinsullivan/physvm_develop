# ROS Tutorial 

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
11. Copy over a launch directory from another project, edit it to contain the nodes you've registered and that you want to launch when the project is ran