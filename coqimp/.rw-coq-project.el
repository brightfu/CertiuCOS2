(setq coq-prog-name (expand-file-name "coqtop" (getenv "coq85bin")))
(setq coq-prog-args `("-R" ,(file-name-directory (buffer-file-name)) "CertiOS"))
