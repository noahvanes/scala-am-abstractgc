(letrec ((counter 0)
         (thread (lambda (n)
                   (letrec ((old counter)
                            (new (+ old 1)))
                     (if (cas counter old new)
                         #t
                         (thread n)))))
(t1 (spawn (thread 1)))
(t2 (spawn (thread 2)))
(t3 (spawn (thread 3)))
(t4 (spawn (thread 4)))
(t5 (spawn (thread 5)))
(t6 (spawn (thread 6)))
(t7 (spawn (thread 7)))
(t8 (spawn (thread 8))))
(join t1)
(join t2)
(join t3)
(join t4)
(join t5)
(join t6)
(join t7)
(join t8))