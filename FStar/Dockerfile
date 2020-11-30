FROM ubuntu:20.04

ENV TZ=Asia/Kolkata
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt update

RUN apt install -y sudo

# Create user
RUN useradd -ms /bin/bash vericrypt
RUN echo "vericrypt ALL=(ALL:ALL) NOPASSWD:ALL" >> /etc/sudoers
USER vericrypt
WORKDIR /home/vericrypt

RUN sudo apt install -y git opam
RUN opam init --disable-sandboxing -y --compiler=4.09.1
RUN opam switch 4.09.1

RUN git clone https://github.com/project-everest/everest.git
COPY --chown=vericrypt:vericrypt everest /home/vericrypt/everest/everest

RUN opam install -y ocamlfind

RUN ./everest/everest --yes opam

RUN sudo apt install -y nodejs fsharp scons

WORKDIR /home/vericrypt/everest

RUN ./everest --yes check

RUN ./everest --yes pull_projects

ENV FSTAR_HOME=/home/vericrypt/everest/FStar
ENV KREMLIN_HOME=/home/vericrypt/everest/kremlin

RUN OTHERFLAGS='--admit_smt_queries true' ./everest -j 4 FStar make
RUN OTHERFLAGS='--admit_smt_queries true' ./everest -j 4 kremlin make

RUN sudo apt-get install -y emacs libglu1-mesa xfonts-terminus fonts-symbola

ENV LANG C.UTF-8
RUN emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'fstar-mode)" \
	--eval "(package-install 'flycheck)"

COPY --chown=vericrypt:vericrypt .emacs /home/vericrypt/.emacs

ENV PATH="/home/vericrypt/everest/FStar/bin:/home/vericrypt/everest/kremlin/:${PATH}"

WORKDIR /home/vericrypt/everest/FStar
