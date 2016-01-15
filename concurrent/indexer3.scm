;; Example taken from Dynamic Partial Order Reduction, Figure 1
;; Expected result: #t
(let* ((size 128)
       (max 4)
       (table (make-vector size 0))
       (thread (lambda (tid)
                 (letrec ((hash (lambda (w) (modulo (* w 7) size)))
                          (process (lambda (m)
                                     (if (< m max)
                                         (letrec ((w (+ (* 11 (+ m 1)) tid))
                                                  (update (lambda (h)
                                                            (if (cas-vector table h 0 w)
                                                                #t
                                                                (update (modulo (+ h 1) size))))))
                                           (update (hash w))
                                           (process (+ m 1)))
                                         #t))))
                   (process 0))))
       (t1 (spawn (thread 1)))
       (t2 (spawn (thread 2)))
       (t3 (spawn (thread 3))))
  (join t1)
  (join t2)
  (join t3)
  (and (= (vector-ref table 84) 12)
       (= (vector-ref table 33) 23)
       (= (vector-ref table 110) 34)
       (= (vector-ref table 59) 45)
       (= (vector-ref table 91) 13)
       (= (vector-ref table 40) 24)
       (= (vector-ref table 117) 35)
       (= (vector-ref table 66) 46)
       (= (vector-ref table 98) 14)
       (= (vector-ref table 47) 25)
       (= (vector-ref table 124) 36)
       (= (vector-ref table 73) 47)))
