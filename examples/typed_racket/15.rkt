#lang typed/racket
(define-type A (Class))
(: A% A)
(define A% (class object%
                 (super-new)
             ))


(define-type B (Class [foo (-> Integer)]))
(: B% B)
(define B% (class A%
                (super-new)
                (define/public (foo)
                  2)
  ))

(define-type C (Class [bar (-> Integer)]))
(: C% C)
(define C% (class A%
                (super-new)
                (define/public (bar)
                  3)
  ))


(define-type D (Class (field (a (Instance A)))
                      (field (b (Instance B)))
                      (field (c (Instance C)))
                      [main (-> Integer)]))
(: D% D)
(define D% (class object%
                (super-new)
                (field (a (make-object A%)))
                (field (b (make-object B%)))
                (field (c (make-object C%)))
                (define/public (main)
                  (set! b (make-object B%))
                  (set! a b)
                  (set! c (cast a (Instance C)))
                  (send b foo))
  ))


(define test (make-object D%))
(send test main)

