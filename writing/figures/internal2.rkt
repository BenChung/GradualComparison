#lang typed/racket
(module untyped racket
  (define A% (class object% (super-new)
               (define/public (foo) "hello")
               (define/public (bar) (send this foo))))
  (define (gen) (make-object A%))
  (provide gen))

(define-type A (Class [foo (-> Integer)] [bar (-> Integer)]))
(require/typed 'untyped [gen (-> (Instance A))])
(send (gen) bar)
