#lang typed/racket

(define-type Fruit (Class [say (-> String)]))
(: Fruit% Fruit)
(define Fruit% (class object%
             (super-new)
             (define/public (say) "")
  ))

(define-type Apple (Class [say (-> String)]))
(: Apple% Apple)
(define Apple% (class Fruit%
             (super-new)
             (define/override (say) "Apple"))
  )

(define-type Banana (Class [say (-> String)]))
(: Banana% Banana)
(define Banana% (class Fruit%
             (super-new)
             (define/override (say) "Banana"))
  )

(define-type Main (Class (field (f (Instance Fruit))) [main (-> String)]))
(: Main% Main)
(define Main% (class object%
             (super-new)
             (field (f (make-object Fruit%)))
             (define/public (main) (set! f (make-object Apple%)) (set! f (make-object Banana%)) (send f say)))
  )

(define test (make-object Main%))
(send test main)