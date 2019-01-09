#lang racket

(define (generate-prog todo vars defs)
  (if (= todo 0)
      `(begin ,@defs 42)
      (let [(v (gensym))]
        (generate-prog (- todo 1)
                       (cons v vars)
                       (cons `(define ,v (+ 1 1)) defs)))))

(define START 1000)
(define STOP 10000)
(define UPDATE (lambda (x) (+ x 1000)))

(let loop [(current START)]
  (when (<= current STOP)
    (with-output-to-file (string-append "/Users/nvanes/Desktop/benchmarks/scalability/" (number->string current) ".scm")
      (lambda () (write (generate-prog current '() '()))))
    (loop (UPDATE current))))