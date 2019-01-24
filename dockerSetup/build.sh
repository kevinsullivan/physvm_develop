#!/bin/bash

# If the LLVM build folder doesn't exist yet, create it.
if [[ ! -d /llvm/build ]]; then
  echo '===---------- Creating /llvm/build folder ----------==='
  mkdir /llvm/build
fi

# Find out what clang is called on here.
which clang++-3.9
if [[ $? -eq 0 ]]; then
  export CXX=clang++-3.9
else
  export CXX=clang++
fi

# If the folder is empty, build it.
echo '===---------- Building LLVM and clang ----------==='
cd /llvm/build
cmake -DCMAKE_BUILD_TYPE=MinSizeRel \
      -DLLVM_ENABLE_ASSERTIONS=OFF \
      -DCMAKE_C_COMPILER=$C \
      -DCMAKE_CXX_COMPILER=$CXX \
      ..
make -j4
cd -

# If the project build folder doesn't exist yet, create it.
#if [[ ! -d /User/isprime/peirce/build ]]; then
#  echo '===---------- Creating /build folder ----------==='
#  mkdir /User/isprime/peirce/build
#fi

# If the folder is empty, build it.
#echo "===---------- Building project on $1 ----------==="
#cd /User/isprime/peirce/build
#cmake -DLLVM_PATH=/llvm \
#      -DCMAKE_BUILD_TYPE=MinSizeRel \
#      -DCMAKE_C_COMPILER=$C \
#      -DCMAKE_CXX_COMPILER=$CXX \
#      -DFIND_LLVM_VERBOSE_CONFIG=on \
#      -DCLANG_EXPAND_OS_NAME=$1 \
#      /User/isprime/peirce/project
#make -j4
#cd -
