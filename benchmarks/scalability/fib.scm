(define (alloc n)
  (if (= n 0)
      '()
      (cons n (alloc (- n 1)))))

(define keep (alloc 1000))

(define (fib n)
  (if (<= n 2)
      n
      (+ (fib (- n 2))
         (fib (- n 1)))))

(fib 10)