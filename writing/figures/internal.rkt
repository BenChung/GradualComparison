#lang typed/racket
(module untyped racket
  (define A% (class object% (super-new)
               (define/public (foo x) x)
               (define/public (bar x) (send this foo x))))
  (define (gen) (make-object A%))
  (provide gen))

(define-type A (Class
                [foo (Integer -> String)]
                [bar (Integer -> Integer)]))
(require/typed 'untyped [gen (-> (Instance A))])
(send (gen) bar 2)
