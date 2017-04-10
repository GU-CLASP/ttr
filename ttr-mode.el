(defvar ttr-mode-hook nil)

;; define several class of keywords
(setq ttr-keywords '("data" "import" "mutual" "let" "in" "data" "split"
                     "module" "where" "open" "primitive") )
(setq ttr-special '("undefined" "Type"))

;; create regex strings
(setq ttr-keywords-regexp (regexp-opt ttr-keywords 'words))
(setq ttr-operators-regexp (regexp-opt '(":" "::" "->" "-o" "=" "\\" "|" "\\" "*" "_" "[" "]" "{" "}" "(" ")") t))
(setq ttr-special-regexp (regexp-opt ttr-special 'words))
(setq ttr-def-regexp "^[[:word:]]+")

;; create the list for font-lock.
;; each class of keyword is given a particular face
(setq ttr-font-lock-keywords
  `((,ttr-keywords-regexp . font-lock-type-face)
    (,ttr-operators-regexp . font-lock-variable-name-face)
    (,ttr-special-regexp . font-lock-warning-face)
    (,ttr-def-regexp . font-lock-function-name-face)))

;; syntax table for comments, same as for haskell-mode
(defvar ttr-syntax-table
  (let ((st (make-syntax-table)))
       (modify-syntax-entry ?\{  "(}1nb" st)
       (modify-syntax-entry ?\}  "){4nb" st)
       (modify-syntax-entry ?-  "_ 123" st)
       (modify-syntax-entry ?\n ">" st)
   st))

;; define the mode
(define-derived-mode ttr-mode prog-mode
  "ttr mode"
  "Major mode for editing TTR files"

  :syntax-table ttr-syntax-table

  ;; code for syntax highlighting
  (setq font-lock-defaults '(ttr-font-lock-keywords))
  (setq mode-name "ttr")
  (setq comment-start "--"))

(provide 'ttr-mode)
