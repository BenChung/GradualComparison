#lang typed/racket

(define-type Mult (Class [main (-> Any)] [mul (-> Integer Integer Integer)]))
(: Mult% Mult)
(define Mult% (class object%
             (super-new)
             (define/public (main) (send this mul 6 6))
             (define/public (mul i j) (if (= i 0) 0 (+ j (mul (- i 1) j))))
  ))


(define test (make-object Mult%))
(send test main)