;; Taken from https://github.com/jensnicolay/abstractmemo
(letrec ((even? (lambda (n) (if (= n 0) #t (odd? (- n 1)))))
         (odd? (lambda (n) (if (= n 0) #f (even? (- n 1))))))
   (even? 5))
(+ 1 2 3 4 5)