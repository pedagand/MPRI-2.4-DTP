;; Work around restriction on literate agda vs. holes (issue #2836)
((nil . ((eval . (eval-after-load "agda2" 
                   '(defun agda2-literate-p () "" 
                           (equal (file-name-extension (buffer-file-name)) "lagda")))))))
