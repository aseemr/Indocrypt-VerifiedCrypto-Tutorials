FROM debian:sid

MAINTAINER Pierre-Yves Strub <pierre-yves@strub.nu>

ENV DEBIAN_FRONTEND noninteractive

RUN \
	apt-get -q -y update && \
	apt-get -q -y dist-upgrade && \
	apt-get -q -y install sudo m4 rsync git curl wget && \
	apt-get -q -y install python3 python3-pip && \
	pip3 install --no-cache-dir pyyaml && \
	apt-get -q -y --no-install-recommends install ocaml-nox opam && \
	apt-get -q -y clean

COPY etc/sudo-ci /etc/sudoers.d/ci

RUN addgroup --gid 2000 user
RUN adduser --disabled-password --gecos "CI" --uid 2000 --gid 2000 user
RUN chmod 440 /etc/sudoers.d/ci

USER    user
WORKDIR /home/user

ENV OPAMYES=true OPAMVERBOSE=1 OPAMJOBS=8

RUN \
	opam init --disable-sandboxing -a && \
	opam switch create -v easycrypt ocaml-base-compiler.4.09.1 && \
	opam clean

RUN \
	opam remote add coq-extra-dev https://coq.inria.fr/opam/extra-dev && \
	opam remote add coq-released  https://coq.inria.fr/opam/released && \
	opam remote add coq-core-dev  https://coq.inria.fr/opam/core-dev && \
	opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git && \
	opam pin add -n jasmin https://github.com/jasmin-lang/jasmin.git && \
	opam pin add -n coq-word https://github.com/jasmin-lang/coqword.git && \
	opam pin add -n coq 8.9.1 && \
	opam install depext && opam depext easycrypt jasmin && \
	opam clean


RUN	opam install --deps-only jasmin easycrypt && opam clean
RUN	opam install jasmin && opam clean
RUN	opam install easycrypt && opam clean

RUN     mkdir -p easycrypt/bin easycrypt/etc
WORKDIR /home/user/easycrypt

ENV CVC4V=1.5 Z3V=4.8.4 Z3SV=.d6df51951f4c

RUN \
	opam depext alt-ergo && opam install alt-ergo && opam clean

RUN \
	wget -O cvc4 https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4V}-x86_64-linux-opt && \
        cp cvc4 bin/ && rm -f cvc4

RUN \
	wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip && \
        unzip -j z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip z3-${Z3V}${Z3SV}-x64-ubuntu-16.04/bin/z3 && \
        cp z3 bin/ && rm -rf z3 z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip

COPY --chown=user:user bin/easycrypt bin/easycrypt
COPY --chown=user:user bin/jasminc bin/jasminc
RUN chmod +x bin/*
ENV PATH="/home/user/easycrypt/bin:${PATH}"

RUN opam config exec -- why3 config -C etc/why3.conf --detect --full-config
COPY --chown=user:user etc/easycrypt.conf ../.config/easycrypt/easycrypt.conf

WORKDIR /home/user

RUN sudo apt-get install -y emacs-nox && sudo apt-get clean

RUN \
    emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'proof-general)" \
	--eval "(package-install 'company-coq)" \
	--eval "(package-install 'opam)"

COPY --chown=user:user etc/emacs .emacs

COPY --chown=user:user contents easycrypt/contents
