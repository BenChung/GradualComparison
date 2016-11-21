#lang racket


(require "typed.rkt"
               [Cowboy%])

(define ShotGun% (class object%
                  (define/public (shoot left num) 
                    (- num 1))
                  (super-new)))

(define bill (make-object Cowboy%))

