## Complete the Onboarding tutorial, found in ONBOARD.md

## Run the Docker Container

1. In a terminal start the docker image for the build environment by running the following command. On Windows (10 Pro), use a PowerShell or CMD window, **not** Git Bash. 
```shell
docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v %YOUR_PEIRCE_MOUNT_OR_OTHER_DIRECTORY_GOES_HERE%:/peirce andrewe8/peirce_docker /bin/bash
```
Make sure to replace the substring starting and ending with the percentage signs above to be the path of your cloned peirce repo directory. 
Note: You can shut down this container from a local terminal window by running 
```shell
docker container stop peirce_docker
```
or by issuing the
```shell
exit
```
command in the terminal window connected to the container.

NOTE: It is important that your local Peirce repo directory be mounted on the VM path, /peirce. 

## Connect VSCode to Container

1. Run VSCode and launch Use the Command Palette (Ctrl + Shift + P)
2. Type in "attach" to trigger auto-complete, then pick *Select ~ "Remote-Containers - Attach to Running Container*"
3. Choose the "peirce_docker" container from the list
4. There should be an "open folder" option that will open a dialog from which you should navigate to "/peirce" (This is the in-VM mount point for your local peirce repository directory if you performed Step 1 correctly.)
5. Be default, VSCode within the container does not have all of your extensions installed. You will likely see a notification that explains that extensions are being installed. If not, proceed to your extensions tab, filter to "installed", click on all recommended extensions, including C/C++ and Clang Command Adapter, and, for all, click on "Install in Container". Click "Reload" when done. 
6. Select the Git panel in VS Code. If you have any pending changes (for the newly cloned directory), use git functions to discard those changes then stop and restart the Docker container. The pending changes should no longer appear. Sorry for this glitch. If things get confusing, ask Prof. Sullivan or another expert for help.

## Building and Running the Project

1. Within the VSCode instance attached to the docker container, open up a terminal.
2. In the terminal, make sure you are locally in the directory /peirce/src. If you aren't, navigate there using cd.
3. Issue teh shell command 
```shell
make clean && make -j 4
```
to build the project. This should take some time.
4. To run on an input file, issue the comand 
```shell
/peirce/src/peirce /peirce/ros/affine_tests/src/affine_tests/src/test1-space_creation-input-PASS.cpp -extra-arg=-I/opt/ros/melodic/include/ < /peirce/src/inp_time.txt
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