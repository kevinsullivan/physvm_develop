# Affine Physics Development Environment

- Fork this repository (won't get submodules)
- Open VSCode Remote Containers on it (won't populate submodules)
- Launch terminal
- Configure git for yourself in terminal/container
  - git config --global user.name "Kevin Sullivan"
  - git config --global user.email sullivan.kevinj@gmail.com
- Copy the container's public key (~/.ssh/ed25519.pub) to your GitHub SSH keys
- In terminal / container:
  - git submodule init
  - git submodule update
