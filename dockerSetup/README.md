# Docker 
This folder contains the Dockerfile to build the llvm/clang infrastructure to parse the source code and also the `build.sh` build script for compile llvm/clang tool chain. So once the docker container is built, then the infrastructure is already there.

Once you cloned this repo, run `cd ./dockerSetup` and then simply run the following command to build the docker image, I'll just name it as ubuntu_clang_image
```
docker build -t ubuntu_clang_image .
```

Afterwards, run the following command to spin up the container. $PWD=path/to/PierceProject.
```
cd path/to/PieceProject

docker run -it --name clang_docker -v llvm-build:/llvm/build -v $PWD:/peirce ubuntu_clang_image /bin/bash
```