#!/bin/bash

# --------------------------------------------------------------------
ROOT="${HOME}/cryptoverif"

# --------------------------------------------------------------------
function error { echo "$@" >&2; exit 1; }

# --------------------------------------------------------------------
[ ! -d "${ROOT}" ] || error "Remove ${ROOT} first"

mkdir "${ROOT}"

cd "${ROOT}"

# --------------------------------------------------------------------
export OPAMROOT="${ROOT}/_opam"
export OPAMYES=true

# --------------------------------------------------------------------
set -ve

sudo apt-get -q -y install m4 ocaml opam vim emacs zlib1g-dev
# zlib1g-dev needed for extracting implementations

opam init --disable-sandboxing -n

eval $(opam config env)
opam install -y ocaml ocamlfind cryptokit conf-m4

# The following block downloads and extracts a CryptoVerif release
wget https://gitlab.inria.fr/prosecco/vericrypt-cryptoverif/-/raw/master/cryptoverif2.04.tar.gz
tar -xzf cryptoverif2.04.tar.gz --strip-components=1

# Compile CryptoVerif
./build

# Add only the cryptoverif executable to the directory
# that we will put in the PATH
mkdir bin
ln -s ${ROOT}/cryptoverif ${ROOT}/bin/cryptoverif


# CryptoVerif in Vim
if [[ ! -f ~/.vim/autoload/plug.vim ]]; then
  curl -fLo ~/.vim/autoload/plug.vim --create-dirs https://raw.githubusercontent.com/junegunn/vim-plug/master/plug.vim  
fi

cat >> ~/.vimrc <<EOF
call plug#begin('~/.vim/plugged')
Plug 'tpope/vim-sensible'
Plug 'tpope/vim-sleuth'
Plug 'mgrabovsky/vim-xverif'
call plug#end()
EOF

vim +PlugInstall +qall

# Install cryptoverif-mode for Emacs
cat >> emacs/config <<EOF
(add-to-list 'load-path "${ROOT}/emacs")

;; This is taken from ${ROOT}/emacs/README
(setq auto-mode-alist
  (cons '("\\.cv[l]?$" . cryptoverif-mode)
  (cons '("\\.ocv[l]?$" . cryptoverifo-mode)
  (cons '("\\.pcv$" . pcv-mode) auto-mode-alist))))
(autoload 'cryptoverif-mode "cryptoverif" "Major mode for editing CryptoVerif code." t)
(autoload 'cryptoverifo-mode "cryptoverif" "Major mode for editing CryptoVerif code." t)
(autoload 'pcv-mode "cryptoverif" "Major mode for editing ProVerif and CryptoVerif code." t)
EOF

cat >> ~/.emacs <<EOF
; CryptoVerif configuration
(load-file "${ROOT}/emacs/config")
EOF



# --------------------------------------------------------------------
export PATH="${ROOT}/bin:${PATH}"
export CRYPTOVERIF_HOME="${ROOT}"

cat >>~/.profile <<EOF
# CryptoVerif PATH
PATH="${ROOT}/bin":"\$PATH"
CRYPTOVERIF_HOME="${ROOT}"
EOF


