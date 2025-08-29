(defun replace-incrementing (pattern replacement)
  (interactive "sPattern: \nsReplacement: ")
  (let ((count 1))
    (while (re-search-forward pattern nil t)
      (let ((repl (format "%s %d" replacement count)))
        (incf count)
        (replace-match repl)))))

  (global-set-key [f4] 'goto-line       )
  (global-set-key [f5] 'replace-regexp  )
  (global-font-lock-mode             t  )
  (setq load-path (cons (expand-file-name ".emacs_modes") load-path))
  (setq-default indent-tabs-mode     nil)
  (setq make-backup-files            nil)
(custom-set-variables
  ;; custom-set-variables was added by Custom -- don't edit or cut/paste it!
  ;; Your init file should contain only one such instance.
 '(case-fold-search t)
 '(current-language-environment "UTF-8")
 '(default-input-method "rfc1345")
 '(global-font-lock-mode t nil (font-lock))
 '(makefile-backslash-column 69)
 '(perl-continued-brace-offset -2)
 '(perl-continued-statement-offset 2)
 '(perl-indent-level 2)
 '(query-user-mail-address nil)
 '(standard-indent 2)
 '(tcl-continued-indent-level 2)
 '(tcl-indent-level 2)
 '(truncate-lines t)
 '(user-mail-address "bka@vitesse.com")
 '(vhdl-basic-offset 2)
 '(vhdl-indent-level 2)
 '(vhdl-upper-case-keywords nil))
(custom-set-faces
  ;; custom-set-faces was added by Custom -- don't edit or cut/paste it!
  ;; Your init file should contain only one such instance.
 )
  (set-face-background 'default      "bisque") ; frame background
  (set-face-foreground 'default      "black") ; normal text
;;  (set-face-font       'default      "*courier-bold-r*120-100-100*")
  (set-face-background 'highlight    "blue") ; Ie when selecting
                                          ; buffers
  (set-face-foreground 'highlight    "yellow")
  (set-face-background 'modeline     "blue") ; Line at bottom
                                          ; of buffer
  (set-face-foreground 'modeline     "white")
;;  (set-face-font       'modeline     "*bold-r-normal*140-100-100*")
  (set-face-background 'isearch      "yellow") ; When highlighting
                                          ; while searching
  (set-face-foreground 'isearch      "red")
  (setq x-pointer-foreground-color   "black") ; Adds to bg color,
                                          ; so keep black
  (setq x-pointer-background-color   "blue") ; This is color
                                          ; you really
                                          ; want ptr/crsr

;; OO-Browser setup

(defvar br-directory "/usr/local/lib/xemacs-19.13/lisp/oobr/")
; Directory where the OO-Browser executable code is kept. It must end with a directory separator character.

;;; For FSF Emacs that does not have hyperbole uncomment the following
;; (setq load-path (cons (concat br-directory "hypb")) load-path)

(autoload 'oo-browser (expand-file-name "br-start" br-directory)
  "Invoke the OO-Browser" t)
(autoload 'br-env-browse (expand-file-name "br-start" br-directory)
  "Browse an existing OO-Browser Environment" t)

; Lets just enable browsing for C++ and Python
; for full list of languages, see br-env.el
(defvar br-env-lang-avector
  '[("C++"     . "c++-")
    ("Python"  . "python-")]
  "Association vector of (LANGUAGE-NAME . LANGUAGE-PREFIX-STRING) elements of OO-Browser languages.")

(global-set-key "\C-c\C-o" 'oo-browser)

(cond 
 (
  (progn
    (load "~/.emacs_dir/python.el")		;; Buffer menu definition (for Python)
    ) ;;progn
  )
 ) ;; cond


(cond 
 (
  (progn
    (load "~/.emacs_dir/verilog-mode.el")		;; Buffer menu definition (for Verilog)
    ) ;;progn
  )
 ) ;; cond

;; Add python mode!
    (setq auto-mode-alist (cons '("\\.py$" . python-mode) auto-mode-alist))
    (setq interpreter-mode-alist (cons '("python" . python-mode)
                                       interpreter-mode-alist))
    (autoload 'python-mode "python-mode" "Python editing mode." t)

;; In XEmacs syntax highlighting should be enabled automatically.  In GNU
;; Emacs you may have to add these lines to your ~/.emacs file:
    (global-font-lock-mode t)
    (setq font-lock-maximum-decoration t)

(put 'downcase-region 'disabled nil)

(defun prepend-path ( my-path ) 
(setq load-path (cons (expand-file-name my-path) load-path))) 

(defun append-path  ( my-path ) 
(setq load-path (append load-path (list (expand-file-name my-path))))) 
;; Look first in the directory ~/elisp for elisp files 
(prepend-path "~/.emacs_dir") 
;; Load verilog mode only when needed 
(autoload 'verilog-mode "verilog-mode" "Verilog mode" t ) 
;; Any files that end in .v, ,sv or .sva should be in verilog mode 
(setq auto-mode-alist (cons '("\\.[v|sv|sva|svh]+\\'" . verilog-mode) auto-mode-alist)) 
;; Any files in verilog mode should have their keywords colorized 
(add-hook 'verilog-mode-hook '(lambda () (font-lock-mode 1))) 




