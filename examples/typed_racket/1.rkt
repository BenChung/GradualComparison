#lang typed/racket

(define main% (class object%
                (init [ia : Integer])
                (init [ib : Any])
                (: a Integer)
                (define a ia)
                (: b Any)
                (define b ib)
                (super-new)
                (: main (-> Integer))
                (define/public (main)
                  a + (cast b Integer))
                ))

(define test (make-object main% 2 4))
(send test main)