# CryptoVerif

## Install manually

Here are some instructions for manual installation. They are based
on Ubuntu, but you might be able to adapt them for your OS.

* You can use the Bash script `install.sh`, we tested it on Ubuntu, and
  used it to install CryptoVerif in the VM.
* Alternatively, install the dependencies:
  * `sudo apt-get install m4 ocaml opam zlib1g-dev`
  * `opam install ocaml ocamlfind cryptokit conf-m4`
* Then, execute the `./build` script in unpacked the CryptoVerif directory.

### Editor support

* For Vim, [mgrabovsky/vim-xverif](https://github.com/mgrabovsky/vim-xverif)
  provides syntax highlighting. See [these lines](https://github.com/aseemr/Indocrypt-VerifiedCrypto-Tutorials/blob/main/cryptoverif/install.sh#L44-L57)
  in the `install.sh` script for some guidance on how to install it with the
  vim-plug plugin manager.
* For Emacs, put the following into your `.emacs`, and replace `${CRYPTOVERIF}`
  by the directory to which you extracted the CryptoVerif archive:
```
(add-to-list 'load-path "${CRYPTOVERIF}/emacs")

(setq auto-mode-alist
  (cons '("\\.cv[l]?$" . cryptoverif-mode)
  (cons '("\\.ocv[l]?$" . cryptoverifo-mode)
  (cons '("\\.pcv$" . pcv-mode) auto-mode-alist))))
(autoload 'cryptoverif-mode "cryptoverif" "Major mode for editing CryptoVerif code." t)
(autoload 'cryptoverifo-mode "cryptoverif" "Major mode for editing CryptoVerif code." t)
(autoload 'pcv-mode "cryptoverif" "Major mode for editing ProVerif and CryptoVerif code." t)
```

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

## Color Problems inside Docker

When you run applications such as emacs inside the terminal in which
you run Docker, colors are controled by the terminal, not by
Docker. Depending on the configuration of the terminal, some colors
may not be very visible.  Possible solutions:

* Run emacs in a new window, by enabling X support. See
https://github.com/FStarLang/FStar/wiki/Running-F%2A-from-a-docker-image
* Use a different terminal. For instance, on Windows, use the command-line instead of Powershell. Depending on your configuration, colors may be different.
* Adjust colors manually. For instance, on Windows, right-click the title bar of the Docker window; in the menu that opens, choose "Properties", then the "Colors" tab. You see the 16 colors represented by 16 squares on a line. First take note of the currently selected color, the one with a black border around the square (the others have a white border); it corresponds to the selected background color. To adjust a color, click on it and modify the red, green, blue quantities. When you are done, click again on the color that was selected at the beginning to restore the background color.
