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
2. 

## Development Workflow