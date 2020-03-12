# Onboarding Overview

This document contains an abbreviated set of steps to be followed to pepare your local machine for Peirce development and to afterwards develop.

## Docker Setup

1. Go to Docker.io
2. Create a user account
3. Contact the Docker administrator for Peirce who will add your account as a collaborator to the Peirce Docker
4. Download Docker for your respective platform and ensure daemon is running
5. Issue the following command: "docker login docker.io -u %MY_DOCKER_LOGIN_HERE% -p "%MY_DOCKER_PASSWORD_HERE%"
6. Next: "docker pull andrewe8/andrewpeircetest". A 3GB file download will ensue. Image name subject to change.
7. Test image with: docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v %YOUR_PEIRCE_MOUNT_OR_OTHER_DIRECTORY_GOES_HERE%:/peirce andrewe8/andrewpeircetest:latest /bin/bash
8. This can be shut off with : "docker container stop peirce_docker"

#### This will need to be updated when UVA's Gitlab Docker Registry is fully working and our image is migrated internally.

## Gitlab Setup

1. Ensure you have an account with and access to https://gitlab.cs.virginia.edu/
2. Obtain developer access to the "Peirce Docker Builder" and "Peirce" repositories if you don't already.
3. Clone both repositories locally

## VSCode Setup

1. Download VSCode
2. You'll need to open a "workspace folder" - select the "peirce" directory, namely, the folder where you cloned your Peirce repository into
3. You should receive a prompt to "Install the Recommended Extensions". Click yes.
4. Should that not appear, please navigate to the extensions tab, click the "...", and filter to "recommended extensions". Download all in that list (4 at the time of writing this)
 
## Running Peirce in VSCode

1. In a terminal: "docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v %YOUR_PEIRCE_DIRECTORY_GOES_HERE%:/peirce andrewe8/andrewpeircetest:latest /bin/bash"
2. In VSCode: Use the Command Palette (Ctrl + Shift + P)
3. Type in "attach" to trigger auto-complete -> Select ~ "Remote-Contaiers - Attach to Running Container"
4. Choose "peirce_docker" from the list
5. There should be an "open folder" option that will open a dialog, from which you should navigate to "/peirce" (This will be the same as your local peirce repository directory if you performed Step 1 correctly).
6. Go to your Extensions
7. Click on C/C++ and Clang Command Adapter, and, for both, click on "Install in Container"
8. You'll (theoretically) be able to build (Ctrl+Shift+B), Debug (F5), and Run (Ctrl+F5)


## Development Workflow

1. Instructions do not vary much between developing on the "Peirce Docker Builder" or "Peirce" project.
2. All work must be done on a "feature branch", thus, create a branch titled "feature/%MY_DESCRIPTIVE_FEATURE-SPECIFIC_BRANCH_NAME%"
3. Switch to that branch for development.
4. Perform development,rigorously test changes, ensure no issues in building
5. Push your changes. 
6. This should trigger a build on GitLab. Navigate to "CI/CD" and check the jobs tab. One should coincide with your push time.
7. If your build succeeds, this should trigger a built image to get pushed to DockerHub with the Docker Project, or, for Peirce, it will upload the built binary as an "artifact" to be downloaded as an attachment to the job itself
8. If it fails, please check the job output to see what triggered the failure. If it was not your fault, contact the Runner administrator (Andrew)
9. When everything is ready, submit a merge request to merge your changes back into the master branch