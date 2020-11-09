FROM fstarlang/fstar-emacs
LABEL maintainer="Benjamin Lipp <benjamin.lipp@inria.fr>"

USER build
WORKDIR /home/build

# Needed for the CryptoVerif build script to find ocamlyacc and ocamllex
ENV PATH="/home/build/.opam/4.07.0/bin:${PATH}"

# conf-m4 ocaml ocamlfind are already installed by fstar
# only needed to extract implementations
#RUN opam install -y cryptokit

# In case we would want to download the release when building,
# swap the ADD lines
#ADD https://prosecco.gforge.inria.fr/personal/bblanche/cryptoverif/cryptoverif2.03pl1.tar.gz .
ADD cryptoverif2.03pl1.tar.gz .
# ADD decompresses local archives, so the following is only
# necessary if the release was downloaded remotely by docker build
#RUN tar -xzf cryptoverif2.03pl1.tar.gz -C cryptoverif --strip-components=1

RUN sudo chown -R build:build cryptoverif2.03pl1
RUN mv cryptoverif2.03pl1 cryptoverif
WORKDIR cryptoverif

# Compile CryptoVerif
RUN ./build

# Add the executable to the PATH
RUN mkdir bin
RUN ln -s $(pwd)/cryptoverif $(pwd)/bin/
ENV PATH="/home/build/cryptoverif/bin:${PATH}"
ENV CRYPTOVERIF_HOME="/home/build/cryptoverif"

WORKDIR /home/build
