#lang racket
 
(provide (struct-out pt)
         distance
         distance2)
 
(struct pt (x y))
 
; distance : pt pt -> real
(define (distance p1 p2)
  (sqrt (+ (sqr (- (pt-x p2) (pt-x p1)))
           (sqr (- (pt-y p2) (pt-y p1))))))

(define (distance2 p1 p2)
  "foo")
