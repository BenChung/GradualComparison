#lang typed/racket

(define-type A (Class [main (-> Any)] [f (-> Any Integer)]))
(: A% A)
(define A% (class object%
             (super-new)
             (define/public (main) (send this f 2))
             (define/public (f i) (cast i Integer))
  ))


(define test (make-object A%))
(send test main)