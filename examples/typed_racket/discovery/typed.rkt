#lang typed/racket
 
(require/typed "untyped.rkt"
               [#:struct pt ([x : Real] [y : Real])]
               [distance (-> pt pt Real)])
 
(distance (pt 3 5) (pt 7 0))