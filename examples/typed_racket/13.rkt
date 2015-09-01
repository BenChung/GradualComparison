#lang typed/racket

(define-type Fruit (Class [say (-> String)]))
(: Fruit% Fruit)
(define Fruit% (class object%
             (super-new)
             (define/public (say) "")
  ))

(define-type Animal (Class [say (-> String)]))
(: Animal% Animal)
(define Animal% (class object%
             (super-new)
             (define/public (say) "")
  ))

(define-type Apple (Class [say (-> String)]))
(: Apple% Apple)
(define Apple% (class Fruit%
             (super-new)
             (define/override (say) "Apple"))
  )

(define-type Cat (Class [say (-> String)]))
(: Cat% Cat)
(define Cat% (class Animal%
             (super-new)
             (define/override (say) "Cat"))
  )

(define-type Main (Class (field (f (Instance Fruit))) [main (-> String)]))
(: Main% Main)
(define Main% (class object%
             (super-new)
             (field (f (make-object Fruit%)))
             (define/public (main) (set! f (make-object Apple%)) (set! f (make-object Cat%)) (send f say))) ;works - structural
  )

(define test (make-object Main%))
(send test main)