(defun lzh/coq-grasp (lemma-name)
  (interactive "sname:")
  (goto-char (point-min))
  ;; delete first 2 lines
  (kill-whole-line)
  (kill-whole-line)
  ;; insert the lemma header
  (re-search-forward "^.*$")
  (replace-match (concat "Lemma " lemma-name ": forall"))
  ;; deal with spliter
  (let ((split-point nil))
    (let ((init-p (point)))
      (re-search-forward "^[ =]*$")
      (replace-match "(\* ================================= \*) ,")
      (forward-line -1)
      (end-of-line)
      (insert ")")
      (setq split-point (point-marker))
      (goto-char init-p))
    ;; add parenthesis
    (re-search-forward " : "  nil t)
    (beginning-of-line-text)
    (insert "(")
    (end-of-line)
    (while (and
            (re-search-forward " : " nil t)
            (< (point) (marker-position split-point)))
      ;; first
      (beginning-of-line-text)
      (insert "(")
      ;; last
      (forward-line -1)
      (end-of-line)
      (insert ")")
      ;; move point
      (forward-line 2)))
  ;; add the last "."
  (let ((init-p (point)))
    (goto-char (point-max))
    (insert ".")
    (goto-char init-p)))