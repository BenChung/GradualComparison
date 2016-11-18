#lang typed/racket

(define-type A (Class [foo (-> Integer)] [bar (-> Integer)]))
(define-type B (Class [foo (-> String)]))
(: A% A)
(define A% (class object%
                (super-new)
                (define/public (foo)
                  2)
                (define/public (bar)
                  2)
  ))

(require/typed "simp1.rkt"
               [id (-> (Instance A) (Instance B))]
               [(id id2) (-> (Instance B) (Instance A))]
               [(id id3) (-> Integer String)])

(send (id2 (id (make-object A%))) foo)
(send (id2 (id (make-object A%))) bar)
