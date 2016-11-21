#lang typed/racket
(define A% (class object%
             (init [ia : Any])
             (: a Any)
             (define a ia)
             (super-new)
                (: getA (-> Any))
                (define/public (getA) a)
                ))
(define B% (class A%
             (init [ia : Integer])
             (: a Integer)
             (define a ia)
             (super-new)
                (: getA (-> Integer))
                (define/public (getA) a)
                ))