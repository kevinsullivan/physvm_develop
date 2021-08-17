# Copyright © 2001 by the Rectors and Visitors of the University of Virginia. 

# Extend Ubunto 20.04
FROM  docker.io/kevinsullivan/leanvm 

# Create image without any user interaction
ENV DEBIAN_FRONTEND=noninteractive
RUN echo 'debconf debconf/frontend select Noninteractive' | debconf-set-selections

RUN ssh-keygen -t ed25519 -C "sullivan@virginia.edu" -f ~/.ssh/ed25519
RUN eval `ssh-agent -s`


# RUN ssh-keygen -t ed25519 -C "sullivan@virginia.edu" -f ~/.ssh/
#Generating public/private ed25519 key pair.
# Enter file in which to save the key (/root/.ssh/id_ed25519): 
# Enter passphrase (empty for no passphrase): 
# Enter same passphrase again: 
# Your identification has been saved in /root/.ssh/id_ed25519
# Your public key has been saved in /root/.ssh/id_ed25519.pub
