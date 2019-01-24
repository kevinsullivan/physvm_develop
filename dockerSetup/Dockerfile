FROM ubuntu
MAINTAINER <peter@goldsborough.me>

# Install packages.
RUN apt-get update  -y \
 && apt-get install -y git cmake vim make wget gnupg

# Get LLVM apt repositories.
RUN wget -O - 'http://apt.llvm.org/llvm-snapshot.gpg.key' | apt-key add - \
 && echo 'deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-3.9 main' \
    >> /etc/apt/sources.list \
 && echo 'deb-src http://apt.llvm.org/xenial/ llvm-toolchain-xenial-3.9 main' \
    >> /etc/apt/sources.list

# Install clang-3.9
RUN apt-get update -y && apt-get install -y clang-3.9

ENV C clang-3.9
ENV CXX clang++-3.9

# Grab LLVM and clang.
RUN git clone --progress --verbose \
    https://github.com/llvm-mirror/llvm.git llvm
RUN git clone --progress --verbose \
    https://github.com/llvm-mirror/clang.git llvm/tools/clang
RUN git clone --progress --verbose \
    https://github.com/llvm-mirror/clang-tools-extra.git llvm/tools/clang/tools/extra
    
# These volumes should be mounted as named volumes.
VOLUME /llvm/build /peirce
VOLUME /home

WORKDIR /home
COPY ./build.sh .

RUN ["chmod", "755","./build.sh"]

CMD ["./build.sh", "ubuntu"]