#lang typed/racket

(define B% (class object%
             (super-new)
             (: tbs (Any Any -> Any))
             (define/public (tbs a b) (+ (cast a Integer) (cast b Integer)))
             (define/public (main) (tbs 2 3))
  ))


(define test (make-object B%))
(send test main)