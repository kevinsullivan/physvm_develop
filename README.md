# Affine Physics Development Environment

This repository is configured to provide a phys development environment when forked and cloned into a VSCode remote container. It should but does not yet do it by pulling a domain image from DockerHub, where that image in turn is built (more easily pulled and pushed) using a host file system repository, edited using host-provided VSCode, and built and the like using host-provided Docker (Desktop).

Next task: Rename/repurpose this project to build the precompiled image, then edit down a fork of it to define the project that will pull the compiled vm and extend it as a development platform through VSCode remote containers with a cloned repo.