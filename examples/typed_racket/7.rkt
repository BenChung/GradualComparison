#lang typed/racket

(define-type A (Class [f (-> Integer)]))
(: A% A)
(define A% (class object%
             (super-new)
             (define/public (f) 1)
  ))

(define-type B (Class [g (-> String)]))
(: B% B)
(define B% (class object%
             (super-new)
             (define/public (g) "meh"))
  )

(define-type DAB (Class [f (-> Integer)] [g (-> String)]))


(define-type D (Class [main ((Instance DAB) Integer -> Any)]))
(: D% D)
(define D% (class object%
             (super-new)
             (define/public (main dab num) (if (= num 0) (send dab f) (send dab g))))
  )
