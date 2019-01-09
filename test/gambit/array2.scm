;;; ARRAY -- One of the Kernighan and Van Wyk benchmarks.
;; reduced number of iterations from 200000 to 200

(define (create-x n)
  (define result (make-vector n))
  (let loop ((i 0))
    (cond
        ((>= i n) result)
        (else
            (vector-set! result i i)
            (loop (+ i 1))))))

(define (create-y x)
  (let* ((n (vector-length x))
         (result (make-vector n)))
    (let loop ((i (- n 1)))
        (cond
            ((< i 0) result)
            (else
                (vector-set! result i (vector-ref x i))
                (loop (- i 1)))))))

(define (my-try n)
  (vector-length (create-y (create-x n))))

(define (go n)
  (let loop ((repeat 1)
             (result '()))
    (if (> repeat 0)
        (loop (- repeat 1) (my-try n))
        result)))

(go 100)
