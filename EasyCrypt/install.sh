#! /bin/bash

# --------------------------------------------------------------------
ROOT="${HOME}/easycrypt"
CVC4V=1.5
Z3V=4.8.4
Z3SV=.d6df51951f4c

# --------------------------------------------------------------------
function error { echo "$@" >&2; exit 1; }

# --------------------------------------------------------------------
# [ ! -d "${ROOT}" ] || error "Remove ${ROOT} first"

mkdir "${ROOT}"
for i in etc bin; do mkdir "${ROOT}/$i"; done

cd "${ROOT}"

export PATH="${ROOT}/bin:${PATH}"

# --------------------------------------------------------------------
export OPAMROOT="${ROOT}/_opam"
export OPAMVERBOSE=1
export OPAMJOBS=4
export OPAMYES=true

# --------------------------------------------------------------------
set -ve

sudo apt-get -q -y install m4 rsync git curl wget python3 python3-pip ocaml opam
sudo pip3 install --no-cache-dir pyyaml

opam init --disable-sandboxing -n
opam switch create -v easycrypt ocaml-base-compiler.4.09.1

eval $(opam config env)

opam remote add coq-extra-dev https://coq.inria.fr/opam/extra-dev
opam remote add coq-released  https://coq.inria.fr/opam/released
opam remote add coq-core-dev  https://coq.inria.fr/opam/core-dev
opam pin add -n easycrypt https://github.com/EasyCrypt/easycrypt.git
opam pin add -n jasmin https://github.com/jasmin-lang/jasmin.git
opam pin add -n coq-word https://github.com/jasmin-lang/coqword.git
opam pin add -n coq 8.9.1
opam install depext && opam depext easycrypt jasmin
opam install jasmin easycrypt

# --------------------------------------------------------------------
read -r -d '' BIN_TEMPLATE <<EOF || true
#! /bin/sh
exec opam config --root="${OPAMROOT}" --switch=easycrypt exec -- "\$(basename \$0)" "\$@"
EOF

for i in easycrypt jasminc; do
  echo "${BIN_TEMPLATE}" > bin/$i
  chmod +x bin/$i
done

# --------------------------------------------------------------------
opam depext alt-ergo && opam install alt-ergo

# --------------------------------------------------------------------
wget -O cvc4 https://cvc4.cs.stanford.edu/downloads/builds/x86_64-linux-opt/cvc4-${CVC4V}-x86_64-linux-opt
chmod +x cvc4 && mv cvc4 "${OPAMROOT}/bin"

# ---------------------------------------------------------------------
wget https://github.com/Z3Prover/z3/releases/download/z3-${Z3V}/z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip
unzip -j z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip z3-${Z3V}${Z3SV}-x64-ubuntu-16.04/bin/z3
chmod +x bin/z3 && mv z3 "${OPAMROOT}/bin"
rm -rf z3-${Z3V}${Z3SV}-x64-ubuntu-16.04.zip

# ---------------------------------------------------------------------
opam config exec -- why3 config -C etc/why3.conf --detect --full-config

# --------------------------------------------------------------------
sudo apt-get install -y emacs

emacs --batch \
	--eval "(require 'package)" \
	--eval "(add-to-list 'package-archives '(\"melpa\" . \"http://melpa.org/packages/\") t)" \
	--eval "(package-initialize)" \
	--eval "(package-refresh-contents)" \
	--eval "(package-install 'proof-general)" \
	--eval "(package-install 'company-coq)"

cat >etc/emacs <<EOF
;; Global settings
(setq inhibit-startup-message t) 
(setq initial-scratch-message nil)

(global-font-lock-mode t)

(line-number-mode   t)
(column-number-mode t)

(global-visual-line-mode 1)

(setq process-adaptive-read-buffering nil)
(setq compilation-scroll-output t)

(setq mouse-drag-copy-region t)

(cua-mode t)
(setq cua-auto-tabify-rectangles nil)
(transient-mark-mode 1)
(setq cua-keep-region-after-copy t)

(global-set-key (kbd "C-s") 'save-buffer)
(global-set-key (kbd "C-f") 'isearch-forward)
(global-set-key (kbd "C-n") 'find-file)
(global-set-key (kbd "C-o") 'find-file)

;; Mouse scrolling in terminal emacs
(xterm-mouse-mode 1)
(global-set-key (kbd "<mouse-4>") 'scroll-down-line)
(global-set-key (kbd "<mouse-5>") 'scroll-up-line)

;; Restart xterm-mouse-mode on USR1
(defun usr1-handler ()
   (interactive)
   (xterm-mouse-mode -1)
   (xterm-mouse-mode  1))
 (global-set-key [signal usr1] 'usr1-handler)

;; auto indent
(when (fboundp 'electric-indent-mode) (electric-indent-mode -1))

;; Tabs
(setq-default c-basic-offset 2)
(setq-default tab-width 2)
(setq-default indent-tabs-mode nil)

;; Initialize MELPA
(require 'package)
(add-to-list 'package-archives '("melpa" . "https://melpa.org/packages/") t)
(package-initialize)

;; Proof-general
(setq proof-splash-enable nil)
(setq proof-colour-locked t)
(setq proof-electric-terminator-enable nil)
(setq proof-three-window-mode-policy 'hybrid)
(setq overlay-arrow-string "")

(add-hook 'coq-mode-hook #'company-coq-mode)

(add-hook 'coq-mode-hook
      (lambda () (add-to-list 'write-file-functions 'delete-trailing-whitespace)))

(setq easycrypt-prog-name "~/easycrypt/bin/easycrypt")

(custom-set-faces
 '(proof-error-face ((t (:foreground "red" :weight bold))))
 '(proof-locked-face ((t (:background "grey" :extend t))))
 '(proof-queue-face ((t (:background "yellow" :extend t))))
 '(proof-tactics-name-face ((t (:foreground "blue")))))
EOF

cat >>~/.emacs <<EOF
; EasyCrypt/Jasmin configuration
(load-file "${ROOT}/etc/emacs")
EOF

# --------------------------------------------------------------------
cat >>~/.profile <<EOF
# EasyCrypt / Jasmin PATH
PATH="${ROOT}/bin":"\$PATH"
EOF

# --------------------------------------------------------------------
mkdir -p ~/.config/easycrypt
cat >~/.config/easycrypt/easycrypt.conf <<EOF
[general]
pp-width = 120
idirs = Jasmin:${OPAMROOT}/easycrypt/lib/jasmin/easycrypt
why3conf = ${ROOT}/etc/why3.conf
EOF

# --------------------------------------------------------------------
opam clean
sudo apt-get clean
