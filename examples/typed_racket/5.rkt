#lang typed/racket

(define B% (class object%
             (super-new)
             (: a Any)
             (field (a 12))
             (: b Any)
             (field (b 21))
             (: foo (Integer Integer -> Integer))
             (define/public (foo a b) (+ a b))
             (define/public (main) (foo
                                    (cast (get-field a this) Integer)
                                    (cast (get-field b this) Integer)))
  ))


(define test (make-object B%))
(send test main)