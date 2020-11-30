(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/") t)
(package-initialize)

(add-to-list 'load-path "~/.emacs.d/packages")

(defun my-fstar-compute-prover-args-using-make ()
  "Construct arguments to pass to F* by calling make."
  (with-demoted-errors "Error when constructing arg string: %S"
    (let* ((fname (file-name-nondirectory buffer-file-name))
            (target (concat fname "-in"))
            (argstr (condition-case nil
                        (car (process-lines "make" "--quiet" target))
                      (error (concat
                              "--use_hints "
                              )))))
            (split-string argstr))))

(setq fstar-subp-prover-args #'my-fstar-compute-prover-args-using-make)
(setq fstar-subp-debug t)

(set-fontset-font t 'unicode (font-spec :name "Courier New") nil 'append)
(set-fontset-font t 'unicode (font-spec :name "Symbola") nil 'append)
(custom-set-variables
 ;; custom-set-variables was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(fstar-flycheck-checker nil)
 '(global-flycheck-mode t)
 '(package-selected-packages (quote (fstar-mode tuareg))))
(custom-set-faces
 ;; custom-set-faces was added by Custom.
 ;; If you edit it by hand, you could mess it up, so be careful.
 ;; Your init file should contain only one such instance.
 ;; If there is more than one, they won't work right.
 '(default ((t (:family "Consolas" :foundry "outline" :slant normal :weight normal :height 150 :width normal)))))


(add-hook 'emacs-lisp-mode-hook 'turn-on-eldoc-mode)
(add-hook 'lisp-interaction-mode-hook 'turn-on-eldoc-mode)
(add-hook 'ielm-mode-hook 'turn-on-eldoc-mode)

(add-hook 'fstar-mode-hook
      (lambda ()
        (flycheck-mode -1)))

(add-hook 'c-mode-hook
      (lambda ()
        (flycheck-mode -1)))

(add-hook 'c++-mode-hook
      (lambda ()
        (flycheck-mode -1)))
