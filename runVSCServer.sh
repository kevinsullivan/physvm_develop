#! /bin/bash

docker run -it --cap-add=SYS_PTRACE --rm --security-opt seccomp=unconfined --name peirce_docker -v llvm-build:/llvm/build -v C:\Users\sulli\Projects\Peirce:/peirce andrewe8/peirce_docker /bin/bash