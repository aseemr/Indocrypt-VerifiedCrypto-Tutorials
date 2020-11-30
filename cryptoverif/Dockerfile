FROM fstarlang/fstar-emacs
LABEL maintainer="Benjamin Lipp <benjamin.lipp@inria.fr>"

USER build
WORKDIR /home/build

RUN sudo apt -y install vim

# Needed for the CryptoVerif build script to find ocamlyacc and ocamllex
ENV PATH="/home/build/.opam/4.07.0/bin:${PATH}"

# conf-m4 ocaml ocamlfind are already installed by the fstar Dockerfile
# only needed to link extracted implementations
RUN sudo apt -y install zlib1g-dev
RUN opam install -y cryptokit

# The following block downloads and extracts a CryptoVerif release
ADD https://prosecco.gforge.inria.fr/personal/bblanche/cryptoverif/cryptoverif2.03pl1.tar.gz .
RUN sudo chown build:build cryptoverif2.03pl1.tar.gz
RUN mkdir cryptoverif
RUN tar -xzf cryptoverif2.03pl1.tar.gz -C cryptoverif --strip-components=1

# Alternatively, the release can sit next to the Dockerfile,
# and then we do not need to extract it, because ADD does automatically.
#ADD cryptoverif2.03pl1.tar.gz .
#RUN sudo chown -R build:build cryptoverif2.03pl1
#RUN mv cryptoverif2.03pl1 cryptoverif

# Compile CryptoVerif
WORKDIR cryptoverif
RUN ./build

# Add only the cryptoverif executable to the PATH
RUN mkdir bin
RUN ln -s $(pwd)/cryptoverif $(pwd)/bin/
ENV PATH="/home/build/cryptoverif/bin:${PATH}"
ENV CRYPTOVERIF_HOME="/home/build/cryptoverif"

WORKDIR /home/build

# Install cryptoverif-mode for Emacs
RUN cp cryptoverif/emacs/cryptoverif.el .emacs.d/
ADD .emacs-cv .emacs-cv
RUN cat .emacs-cv >> .emacs

# CryptoVerif in Vim
RUN curl -fLo ~/.vim/autoload/plug.vim --create-dirs https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim
ADD .vimrc .vimrc
RUN vim +PlugInstall +qall
