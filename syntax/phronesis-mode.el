;;; phronesis-mode.el --- Major mode for Phronesis policy language -*- lexical-binding: t; -*-

;; Copyright (C) 2026 Jonathan D.A. Jewell
;; Author: Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
;; Version: 0.2.0
;; Package-Requires: ((emacs "24.3"))
;; Keywords: languages
;; URL: https://github.com/hyperpolymath/phronesis
;; SPDX-License-Identifier: MPL-2.0

;;; Commentary:

;; This package provides a major mode for editing Phronesis policy files.
;; Phronesis is a consensus-gated policy language for network configuration.

;;; Code:

(defconst phronesis-mode-syntax-table
  (let ((table (make-syntax-table)))
    ;; Comments
    (modify-syntax-entry ?# "<" table)
    (modify-syntax-entry ?\n ">" table)
    ;; Strings
    (modify-syntax-entry ?\" "\"" table)
    (modify-syntax-entry ?\' "\"" table)
    ;; Operators
    (modify-syntax-entry ?. "." table)
    (modify-syntax-entry ?= "." table)
    (modify-syntax-entry ?< "." table)
    (modify-syntax-entry ?> "." table)
    (modify-syntax-entry ?! "." table)
    (modify-syntax-entry ?& "." table)
    (modify-syntax-entry ?| "." table)
    table)
  "Syntax table for `phronesis-mode'.")

(defconst phronesis-font-lock-keywords
  (list
   ;; Keywords
   '("\\<\\(POLICY\\|CONST\\|IMPORT\\|IF\\|THEN\\|ELSE\\|AND\\|OR\\|NOT\\|IN\\)\\>" . font-lock-keyword-face)
   ;; Actions
   '("\\<\\(ACCEPT\\|REJECT\\|REPORT\\|EXECUTE\\|BLOCK\\)\\>" . font-lock-builtin-face)
   ;; Metadata
   '("\\<\\(PRIORITY\\|EXPIRES\\|CREATED_BY\\|AS\\)\\>" . font-lock-preprocessor-face)
   ;; Test keywords
   '("\\<\\(TEST\\|SCENARIO\\|GIVEN\\|EXPECT\\|DESCRIBE\\|IT\\)\\>" . font-lock-type-face)
   ;; Types
   '("\\<\\(TYPE\\|Integer\\|String\\|Boolean\\|Float\\|List\\|Map\\|Route\\)\\>" . font-lock-type-face)
   ;; Constants
   '("\\<\\(true\\|false\\|nil\\|null\\|never\\|always\\)\\>" . font-lock-constant-face)
   ;; Standard library
   '("\\<Std\\.\\(RPKI\\|BGP\\|Consensus\\|Temporal\\)\\.[a-zA-Z_][a-zA-Z0-9_]*\\>" . font-lock-function-name-face)
   ;; Numbers
   '("\\<[0-9]+\\(\\.[0-9]+\\)?\\([eE][+-]?[0-9]+\\)?\\>" . font-lock-constant-face)
   '("\\<0[xX][0-9a-fA-F]+\\>" . font-lock-constant-face)
   ;; Policy names
   '("POLICY\\s-+\\([a-zA-Z_][a-zA-Z0-9_]*\\)" 1 font-lock-variable-name-face)
   ;; String interpolation
   '("\\${[^}]+}" . font-lock-variable-name-face))
  "Font lock keywords for `phronesis-mode'.")

(defvar phronesis-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map (kbd "C-c C-c") 'phronesis-run-file)
    (define-key map (kbd "C-c C-k") 'phronesis-check-file)
    (define-key map (kbd "C-c C-p") 'phronesis-parse-file)
    (define-key map (kbd "C-c C-r") 'phronesis-repl)
    map)
  "Keymap for `phronesis-mode'.")

(defvar phronesis-indent-offset 2
  "Indentation offset for Phronesis code.")

(defun phronesis-indent-line ()
  "Indent current line as Phronesis code."
  (interactive)
  (let ((indent-col 0)
        (cur-indent (current-indentation)))
    (save-excursion
      (beginning-of-line)
      (cond
       ;; Inside POLICY block
       ((looking-at "\\s-*\\(THEN\\|PRIORITY\\|EXPIRES\\|CREATED_BY\\)")
        (setq indent-col phronesis-indent-offset))
       ;; After POLICY keyword
       ((save-excursion
          (forward-line -1)
          (looking-at "\\s-*POLICY"))
        (setq indent-col phronesis-indent-offset))
       ;; Default: no indent
       (t (setq indent-col 0))))
    (if (< cur-indent indent-col)
        (indent-line-to indent-col)
      (save-excursion (indent-line-to indent-col)))
    (when (> cur-indent indent-col)
      (move-to-column indent-col))))

(defun phronesis-run-file ()
  "Run the current Phronesis file."
  (interactive)
  (compile (format "phronesis run %s" (buffer-file-name))))

(defun phronesis-check-file ()
  "Check syntax of the current Phronesis file."
  (interactive)
  (compile (format "phronesis check %s" (buffer-file-name))))

(defun phronesis-parse-file ()
  "Parse and display AST of the current Phronesis file."
  (interactive)
  (compile (format "phronesis parse %s" (buffer-file-name))))

(defun phronesis-repl ()
  "Start a Phronesis REPL."
  (interactive)
  (start-process "phronesis-repl" "*phronesis-repl*" "phronesis" "repl")
  (switch-to-buffer-other-window "*phronesis-repl*"))

;;;###autoload
(define-derived-mode phronesis-mode prog-mode "Phronesis"
  "Major mode for editing Phronesis policy files."
  :syntax-table phronesis-mode-syntax-table
  (setq-local font-lock-defaults '(phronesis-font-lock-keywords))
  (setq-local comment-start "# ")
  (setq-local comment-end "")
  (setq-local indent-line-function 'phronesis-indent-line))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.phr\\'" . phronesis-mode))

(provide 'phronesis-mode)
;;; phronesis-mode.el ends here
