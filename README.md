# Mathematical Physics Development Environment Development Environment

You're here because, in just a few clicks, you *want* to create a complete, running, working mathematical physics development environment (MPDE) and supporting infrastructure for a new project that can build our libraries of foundationally formalized mathematical physics. 

Good news! Just follow the next few steps to instantiate a VSCode Window, opened to edit a containerized GitHub-backed fork and a local, containerized clone of this repository served up by a full Lean development environment based on Ubuntu 20.04 LTS. 

## System Requirements:

- VSCode and DockerDesktop on a Windows 10 or MacOS machine. In own experience, Docker Desktop hasn't worked well on Windows 10 Home; so Pro, Enterprise, or Education might be needed. Students should check with their educational institutions to see if they are entitled to free upgrades under instititional agreements with Microsoft.
- 16 GB memory  (might work with 8)
- quad-core CPU (haven't tested dual core)

## Features

Features of the provided development environment include the following:

- Cloning this repository properly from within VS Code will automatically build your complete working environment.
- You will have a new fork of this project as one of your own, new GitHub repositories
- Docker will launch our container technology to build and boot up your development environment. 
- You will have Ubuntu 20.04 LTS, Lean Prover (Community), mathlib, Python3, and other nice features.
- VSCode is a development environment preferred and well supported by the Lean Prover Community

## What To Do
- Update your operating system:
  - If MacOS: Be sure your OS is completely up-to-date (current version of Big Sur, currently 11.5.2 as of this writing).
  - If Windows 10 Home: Update to Windows 10 Education (Windows 10 Home won't do). If you're a UVa student, updating to Windows 10 Education is free.
    1. Get OS Windows Update license key from ITS: https://virginia.service-now.com/its/.  
    2. Click Software in the left-hand navigation. Select the *latest* Windows 10 Education version. Get an update key.
    3. After obtaining the OS key, copy and paste it in to the Windows Activation page (same screen as Windows Update).
    4. Reboot your machine. You can check the Windows *System Information* app to confirm that your OS is updated.
- Have a GitHub account. Create one for yourself if necessary. It's free: https://github.com/
- Install Docker Desktop: https://www.docker.com/products/docker-desktop.
- Install VSCode: https://code.visualstudio.com/download.
- Launch Docker Desktop and watch for it to complete its start-up procedures. While it starts up, continue on to the remaining instructions. 
- Use GitHub to fork this repository now. 
  - Be logged in to your GitHub account.
  - Visit this very repository on GitHub (which is probably where you're reading this)
  - Fork this repo using the *Fork* button in the upper right corner. 
  -   This will create a copy of this entire repository in *your* GitHub account. Visit your GitHub page to confirm that you now have a clone of this repository. 
  -   Select the green Code button, then HTTPS, then copy the URL that is provided. This will be the GitHub URL of your newly forked copy of the respository.
- Open our Lean Development Environment directly from your new GitHub repository
  - Launch a *new* VSCode window. 
  - Use CTRL/CMD-SHIFT-P to bring up the VSCode command palatte. 
  - Search for and select *Clone Repository in Container Volume*
  - Paste the URL of your new repository as the argument.
  - If it asks, select *unique repository*.
- Wait for your development environment to completely "boot up" before taking any further actions.
- Check to see that everything is working
  - Open the test.lean file (src/test/test_lean_mathlib.lean)
  -Check that the conditions described therein are satisfied.

## How It Works
We deliver a Lean development environment via VSCode and its *Remote-Containers* capabilities. In a nutshell, when you ask VSCode to clone our repository, it will actually fork it and then clone your fork into the container that it launches to provide the programming platform you will then use to develop your solutions. It is very important to commit changes you make to your container-local repository, but then also to push them to your GitHub repo to back them up and because that should be the main respository for your project. You can log into it by simply opening a Terminal in VSCode. The clone of your repo is in the /workspaces folder within the container file system (or storage *volume*, as it's called).

## Risk Alert and Avoidance
It is important to understand that commits made to git are stored in the Docker container serving up the develop environment.  if you delete the container or its storage volume (which you could do through Docker Desktop), this will erase the work stored in the container. To make your container-local changes persistent, stage/add and then commit your local changes to the local repo, then push your container-repo-local changes to your repository on GitHub. 

## Help Make It Even Better
Let us know what you think. Better yet, make it better and send us a PR. You'll be completely set up to do that by the results of this procedure. 


## Legal and contact
Copyright: © 2021 By the Rector and Visitors of the University of Virginia.
Supervising Author: Kevin Sullivan. UVa CS Dept. sullivan@virginia.edu. 
Acknowledgements: Thank you to multiple students for read, test, and fixing.

## Context

As part of a larger project, we are developing a constructive formalization of mathematical physics, starting with easy classical physics, with the goal of supporting linked abstract/analytic/coordinate-free, and parametric/synthetic/coordinatized, forms of physical (abstract) and computational (parametric) cyber-physical expression, where expressions are atomatically checked for dimensional consistency. Dimensional consistency in our view is both broad in scope and deep in mathematical structure, as suggested by Terrence Tao in his 2012 essay, "A mathematical formalization of dimensional analysis," (December 29, 2012),  https://terrytao.wordpress.com/2012/12/29/a-mathematical-formalisation-of-dimensional-analysis/. One impact of this work will be to eliminate a whole class of commonplace and dangerous software errors, those due to divergences between the physical dimensions of what software is meant to represent and what, if anything, it actually means.



## Old version

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
