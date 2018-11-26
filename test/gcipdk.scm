;; Taken from https://github.com/jensnicolay/abstractmemo
;; Expected result: 36

(letrec ((plusk (lambda (a b k) (k (+ a b))))
         (multk (lambda (a b k) (k (* a b))))
         (idk (lambda (x k) (k x)))
         (fk (lambda (n k)
              (if (<= n 1)
                (k 1)
                (fk (- n 1) (lambda (res) (multk n res k))))))
         (gk (lambda (n k)
              (if (<= n 1)
                (k 1)
                (gk (- n 1) (lambda (res) (multk n n (lambda (n2) (plusk n2 res k)))))))))
  (idk fk (lambda (res-idf)
            (res-idf 3 (lambda (res-f3)
                         (idk gk (lambda (res-idg)
                                 (res-idg 4 (lambda (res-g4)
                                               (+ res-f3 res-g4))))))))))
