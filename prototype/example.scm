(load "sefer.scm")

; displays how many numbers are greater than 2, modulo 5
(sefer-run
 (sefer-pipeline
  `((,iter-map ,(lambda (s) (string->number s)))
    (,iter-map ,(lambda (x) (modulo x 5)))
    (,iter-filter ,(lambda (x) (> x 2)))
    (,iter-count))))
