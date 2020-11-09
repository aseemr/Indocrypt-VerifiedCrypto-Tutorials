# CryptoVerif

## Run from Docker

* Build a docker image from the Dockerfile using `docker build .`
* Use `docker image ls` to find the image's ID
* Use `docker run -it $IMAGE_ID` to launch a container from this image.
  This will give you a shell inside the container.
  Use `exit` or Ctrl+D to close the shell.
* Use `docker ps -a` to find the container's ID
* Use `docker start -i $CONTAINER_ID` to get a shell again in this
  same container.

See https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image
for more guidance on Docker.

## Connectivity Problems from inside Docker

- [Check DNS settings](https://docs.docker.com/engine/install/linux-postinstall/#specify-dns-servers-for-docker)
