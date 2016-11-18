#lang typed/racket


(define-type A (Class [getN (-> Integer)]))

(: A% A)
(define A% (class object%
             (super-new)
             (: getN (-> Integer))
             (define/public (getN) 2)
             ))

(define-type C (Class [getN (-> Integer)]))
(define C% (class A%
             (super-new)
             (: getN (-> Integer))
             (define/override (getN) 4)
                ))

(define D% (class object%
             (super-new)
             (: main (-> (Instance C)))
             (define/public (main)
               (: ref (Instance C))
               (define ref (make-object C%))
               (: anyref Any)
               (define anyref ref)
               (cast anyref (Instance C))
               )))

(define test (make-object D%))
(send test main)