# Onboarding Overview

This document contains an abbreviated set of steps to be followed to pepare your local machine for Peirce development.

## Docker Setup

1. Download Docker for your respective platform (https://www.docker.com/products/docker-desktop) and ensure daemon is running. Make an account with Docker and get permission from the owner of the docker to pull the current image (owner as of 5/26/2020 is Andrew Elsey).
2. Issue the following command in a terminal window:
```shell
docker login
```
The terminal will prompt you for a username and password, you should supply these.
3. Next, issue the following command after ensuring you have permission to access the docker: 
```shell
docker pull andrewe8/peirce_docker
```
A several GB file download will ensue. Image name subject to change. (If you skip this step, the image will be pulled by the next command.)

4. Test image:
```shell
docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v %YOUR_PEIRCE_MOUNT_OR_OTHER_DIRECTORY_GOES_HERE%:/peirce andrewe8/peirce_docker /bin/bash
```
Make sure to replace the substring starting and ending with the percentage signs above with your peirce mount directory. 
5. This can be shut off with the following command in a new terminal window: 
```shell
docker container stop peirce_docker
```
or the following command in the same terminal window:
```shell
exit
```
#### NOTE: It is important that you mount your local directory to /peirce . The path variables use locations within /peirce

## Github Setup

1. Ensure you have an account with Github.
2. Obtain developer access to https://github.com/kevinsullivan/Peirce, https://github.com/kevinsullivan/phys, and https://github.com/drewjel/PeirceDocker.
3. Clone both repositories locally.
4. In your local Peirce repository directory, type the following to download dependencies
```shell
git submodule update --init --recursive
```
This step may fail if you do not have access to any submodules, (for example, phys, which is another Github project).


## VSCode Setup

1. Download VSCode
2. You'll need to open a "workspace folder" - select the "peirce" directory, namely, the folder where you cloned your Peirce repository into
3. You should receive a prompt to "Install the Recommended Extensions". Click yes.
4. Should that not appear, please navigate to the extensions tab, click the "...", and filter to "recommended extensions". Download all in that list (13 at the time of writing this)

## Running Peirce in VSCode

1. In a terminal start the docker image for the build environment. On Windows (10 Pro), use a Windows CMD window, not Git Bash. 
```shell
docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v %YOUR_PEIRCE_DIRECTORY_GOES_HERE%:/peirce andrewe8/peirce_docker /bin/bash
```
3. In VSCode: Use the Command Palette (Ctrl + Shift + P)
3. Type in "attach" to trigger auto-complete -> Select ~ "Remote-Containers - Attach to Running Container"
4. Choose "peirce_docker" from the list
5. There should be an "open folder" option that will open a dialog, from which you should navigate to "/peirce" (This will be the same as your local peirce repository directory if you performed Step 1 correctly).
6. Go to your Extensions
7. VSCode does not have all of your extensions installed by default within the container context. After you are attached to the container, you will likely receive an installation prompt as you did in section VSCode Setup, Step 4. If not, proceed to your extensions tab, filter to "installed", click on all recommended extensions, including C/C++ and Clang Command Adapter, and, for all, click on "Install in Container". This will likely require you to click "Reload", afterwards
8. You'll now be able to build (Ctrl+Shift+B), Debug (F5), and Run (Ctrl+F5)

## Running Mathlib within the container
1. Once you're in the container in vscode, open up a terminal window within VSCode (Terminal -> New Terminal). 
2. cd into the peirce/deps/phys directory, and switch into the affine branch (THIS WILL CHANGE TO MASTER BRANCH IN FUTURE). Use git checkout affine.
3. Run leanpkg configure, and after that finishes, run leanpkg build. This should take a significant amount of time, and will possibly output some errors. Ignore these, and let it run to completion. After this finishes running, you should have a working Mathlib inside of the container. 


## Development Workflow

1. Instructions do not vary much between developing on the "Peirce Docker Builder" or "Peirce" project.
2. All work must be done on a "feature branch", thus, create a branch titled "feature/%MY_DESCRIPTIVE_FEATURE-SPECIFIC_BRANCH_NAME%"
3. Switch to that branch for development.
4. Perform development,rigorously test changes, ensure no issues in building
5. Push your changes. 
6. Once you've confirmed that everything works as intended, and you've finished developing on the branch, you can issue a merge request with master.
