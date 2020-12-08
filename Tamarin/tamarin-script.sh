#!/usr/bin/bash

# Pull required packages
sudo apt install graphviz maude wget unzip

# wget or curl or something
# tar 
wget https://github.com/aseemr/Indocrypt-VerifiedCrypto-Tutorials/raw/main/Tamarin/tamarin-prover-1.6.0-linux64-ubuntu.tar.gz
tar zxvf tamarin-prover-1.6.0-linux64-ubuntu.tar.gz

wget https://github.com/aseemr/Indocrypt-VerifiedCrypto-Tutorials/raw/main/Tamarin/tamarin_examples.zip
unzip tamarin_examples.zip


