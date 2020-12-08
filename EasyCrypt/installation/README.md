# Installation instruction

We provide two ways to build the EasyCrypt & Jasmin tools.

## Docker based

We provide a [Docker](https://www.docker.com/) build file in
`docker/`. To build the tools (assuming that you have installed
docker), execute:

    docker build -t ecjasmin docker

This will create a Docker image that contains the EasyCrypt & Jasmin
tools, along with a configured (text only) Emacs.

You can then enter the Docker image by executing:

    docker run -ti ecjasmin /bin/bash "$PWD/materials":/home/user/materials

All the course materials will be located in the subdirectory
"materials" in the Docker image. The tools' binaries are in the path
under the names `easycrypt` & `jasminc`. You can use Emacs to use
EasyCrypt in interactive mode. Simply open a file that ends with the
`.ec` or `.eca` extension.

## Installation script

We provide a script (`install.sh`) that downloads & compiles EasyCrypt
& Jasmin. The script has been tested on Ubuntu 20.04 (and requires at
least a Debian based system). It requires `sudo` access for installing
needed system packages (.deb) from the official repositories. It
installs the tools in the directory `easycrypt` under your home
directory and updates your `~/.profile` and `~/.emacs` configuration
files (or creates them if they do not exist).

The tools' binaries are added to your path under the names `easycrypt`
& `jasminc`. You can use Emacs to use EasyCrypt in interactive
mode. Simply open a file that ends with the `.ec` or `.eca` extension.
