# Affine Physics Development Environment

This repository is configured to provide a phys development environment when forked and cloned into a VSCode remote container. It should but does not yet do it by pulling a domain image from DockerHub, where that image in turn is built (more easily pulled and pushed) using a host file system repository, edited using host-provided VSCode, and built and the like using host-provided Docker (Desktop).

Next task 1: Rename/repurpose this project to build the precompiled image, then edit down a fork of it to define the project template, each fork of which will pull the compiled vm and build something using it. Common project platform, diverse and decentralized client developments but with PR mechanism to bring advances from the field back into the project easily.

Next task 2: Refactor Peirce DockerBuilder to build from the image produced by the previous step. We will have:

- Platform
  - We maintain this
  - Product is development environment image
  - no .devcontainer directory
- Project
  - Customer creates new instance
  - It provides VSCode dev environment and a place to build new stuff
  - .devcontainer directory, each fork (project) has Dockerfile with hooks to extend platform image

Next task 3: Create a project instance for working with Andrew on his case studies
Next task 4: Create a project instance for the rest of Peirce
  