#lang typed/racket
 
(require/typed "untyped.rkt"
               [#:struct pt ([x : Real] [y : Real])]
               [distance (-> pt pt Real)]
               [distance2 (-> pt pt Real)])
 
(distance (pt 3 5) (pt 7 0))

(define x (distance2 (pt 3 5) (pt 7 0)))
x