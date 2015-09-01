#lang typed/racket
(define-type B (Class [foo (-> Integer)]))
(: B% B)
(define B% (class object%
                (super-new)
                (define/public (foo)
                  2)
  ))

(define-type C (Class [foo (-> Any)]))
(: C% C)
(define C% (class object%
                (super-new)
                (define/public (foo)
                  3)
  ))


(define-type D (Class (field (b (Instance B)))
                      (field (c (Instance C)))
                      [main (-> Integer)]))
(: D% D)
(define D% (class object%
                (super-new)
                (field (b (make-object B%)))
                (field (c (make-object C%)))
                (define/public (main)
                  (set! c (make-object C%))
                  (set! b (cast c (Instance B)))
                  (send b foo))
  ))


(define test (make-object D%))
(send test main)

