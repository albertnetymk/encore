;; By Elias Castegren (elias.castegren@it.uu.se)
;; Feel free to use and modify this file however you see fit.
;; Please e-mail me with comments and suggested changes if
;; you have any.
;;
;; This mode gives syntax highlighting and Haskell-mode-style
;; cyclic indentation for the mylittlepony version of encore.
;;
;; Put this file where Emacs can find it and require it in your
;; init-file. There is a hook to enable encore-mode for all files
;; with extension .enc.

(setq encore-keywords '("class" "def" "else" "get" "if" "in" "let" "new" "print" "skip" "then" "while"))
(setq encore-constants '("true" "false" "null"))
(setq encore-primitives '("int" "string" "void"))

(setq encore-keywords-regexp (regexp-opt encore-keywords 'words))
(setq encore-constants-regexp (regexp-opt encore-constants 'words))
(setq encore-primitives-regexp (regexp-opt encore-primitives 'words))
(setq encore-types-regexp "\\<[A-Z][a-zA-Z]*\\>")
(setq encore-function-regexp "\\<def\\> \\([^(]*\\)([^)]*)\\W*:\\W*.*")
(setq encore-variable-regexp "\\<\\([A-Za-z0-9_]*\\)\\>\\W*:")
(setq encore-comment-regexp "--.?*")

(setq encore-font-lock-keywords
 `(
    (,encore-comment-regexp    . font-lock-comment-face)
    (,encore-keywords-regexp   . font-lock-keyword-face)
    (,encore-constants-regexp  . font-lock-constant-face)
    (,encore-primitives-regexp . font-lock-type-face)
    (,encore-types-regexp      . font-lock-type-face)
    (,encore-function-regexp   1 font-lock-function-name-face)
    (,encore-variable-regexp   1 font-lock-variable-name-face)
  )
)

(setq encore-tab-width 2)
(make-local-variable 'encore-tab-width)

(defun current-line ()
  ""
  (buffer-substring-no-properties (line-beginning-position) (line-end-position)))

(defun first-word ()
  ""
  (let* ((current-line (current-line))
        (word-start (string-match "[^ \t]" current-line))
        (word-end (string-match "[^a-zA-Z]" current-line word-start)))
    (substring-no-properties current-line word-start word-end)))

(defun classify-indent (line first)
  "Give the proper indentation of a line below the current one"
  (if (equal first "class")
      0

  (if (equal first "def")
      (if (string-match "\\<def\\>" line)
          (match-beginning 0)
      (if (string-match "\\<class\\>" line)
          (+ (match-beginning 0) encore-tab-width)))

  (if (string-match "\\<class\\> .*" line)
      (+ (match-beginning 0) encore-tab-width)

  (if (string-match "\\<if\\>.*\\<then\\>.*\\<else\\>" line)
      (match-beginning 0)
  (if (string-match "\\<if\\>.*\\<then\\>" line)
      (if (equal first "else")
          (match-beginning 0)
        (+ (match-beginning 0) encore-tab-width))
  (if (string-match "\\<then\\>" line)
      (if (equal first "else")
          (match-beginning 0)
        (+ (match-beginning 0) encore-tab-width))
  (if (string-match "\\<if\\>.*" line)
      (if (or (equal first "then") (equal first "else"))
          (match-beginning 0)
        (let ((indent (string-match "[^ \t]" line (+ (match-beginning 0) 2)))) (if indent indent (+ (match-beginning 0) encore-tab-width))))
  (if (string-match "\\<else\\>.*" line)
        (+ (match-beginning 0) encore-tab-width)

  (if (string-match "\\<while\\>" line)
      (+ (match-beginning 0) encore-tab-width)

  (if (string-match "\\<def\\>" line)
      (+ (match-beginning 0) encore-tab-width)

  (if (string-match "\\<let\\>.*\\<in\\>$" line)
        (+ (match-beginning 0) encore-tab-width)
  (if (string-match "\\<let\\>" line)
      (if (equal "in" first)
          (match-beginning 0)
        (+ (match-beginning 0) encore-tab-width))
  (if (string-match "\\<in\\>[ \t]*$" line)
      (+ (match-beginning 0) encore-tab-width)
  (if (string-match "\\W*\\([^;]*\\);" line)
      (match-beginning 1)
  (if (bobp)
      0))))))))))))))))

(setq encore-checked-line nil)
(make-local-variable 'encore-checked-line)

(setq encore-last-indent 100)
(make-local-variable 'encore-last-indent)

(setq encore-indent-trigger-commands
  '(indent-for-tab-command yas-expand yas/expand))

(defun encore-indent-line ()
  "Indent current line as encore code"
  (interactive)
  (save-excursion
    (beginning-of-line)
    (if (bobp)
        (indent-line-to 0)
      (let ((indent) (first (first-word)))
        (save-excursion
          (if (memq last-command encore-indent-trigger-commands)
              (progn
                (goto-char (point-min))
                (forward-line (1- encore-checked-line)))
            (progn
              (setq encore-checked-line (line-number-at-pos))
              (setq encore-last-indent 100)))
          (while (and (< 1 (line-number-at-pos)) (or (not indent) (and (> indent encore-tab-width) (>= indent encore-last-indent))))
            (forward-line -1)
            (setq indent (classify-indent (current-line) first))
            (setq encore-checked-line (line-number-at-pos))))
        (if (not indent) (setq indent 0))
        (indent-line-to indent)
        (if (<= indent encore-tab-width)
            (progn
              (setq encore-checked-line (line-number-at-pos))
              (setq encore-last-indent 100))
          (setq encore-last-indent indent)))))
  (if (looking-back "^[ \t]*") (back-to-indentation))
)

(define-derived-mode encore-mode prog-mode
  (setq font-lock-defaults '(encore-font-lock-keywords))
  (setq mode-name "Encore")
  (set (make-local-variable 'indent-line-function) 'encore-indent-line)
)

;; Open "*.enc" in encore-mode
(add-to-list 'auto-mode-alist '("\\.enc\\'" . encore-mode))

(provide 'encore-mode)