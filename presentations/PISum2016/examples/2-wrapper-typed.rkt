#lang typed/racket

(define-type Cowboy (Class [draw (Integer -> Integer)]))
(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw num) 
                    (- num 1))
                  (super-new)))

(define-type Painter (Class [draw (String -> String)]))
(: Painter% Painter)
(define Painter% (class object%
                   (define/public (draw color)
                   (string-join (list "Pretty" color "picture")))
                   (super-new)))

(define painter (make-object Painter%))
(send painter draw "blue")

(: test (-> (Instance Cowboy) Integer Integer))
(define (test subj obj)
   (send subj draw obj))

(require/typed "2-untyped.rkt"
               [id (-> (Instance Painter) (Instance Cowboy))])
3	       
(test (id painter) 8)
