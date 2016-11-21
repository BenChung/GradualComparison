#lang typed/racket

(define-type A (Class [foo (-> Integer)]))

(: A% A)
(define A% (class object%
             (super-new)
             (define/public (foo) 1)
             ))


(define-type B (Class [foo (-> String)] [bar (-> Integer)]))

(: B% B)
(define B% (class object%
             (super-new)
             (define/public (foo) "meh")
             (define/public (bar) 2)
             ))


(define-type D (Class
                (field (ref (Instance A)))
                (field (anyref Any))
                [main (-> (Instance B))]))

(: D% D)
(define D% (class object%
             (field (ref (make-object A%)))
             (field (anyref (make-object A%)))
             (super-new)
             (define/public (main)
               (set! ref (make-object A%))
               (set! anyref ref)
               (cast anyref (Instance B))
             )))


(define test (make-object D%))
(send test main)