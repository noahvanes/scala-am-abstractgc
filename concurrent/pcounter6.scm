(letrec ((counter 0)
         (f (lambda ()
              (letrec ((old counter)
                       (new (+ old 1)))
                (if (cas counter old new)
                    #t
                    (f)))))
         (t1 (spawn (f)))
         (t2 (spawn (f)))
         (t3 (spawn (f)))
         (t4 (spawn (f)))
         (t5 (spawn (f)))
         (t6 (spawn (f))))
  (join t1)
  (join t2)
  (join t3)
  (join t4)
  (join t5)
  (join t6)
  (= counter 6))