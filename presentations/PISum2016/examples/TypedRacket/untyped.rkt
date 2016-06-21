#lang racket
(provide id di)
(define (id x) x)
(define (di x) x)




(define ShotGun% (class object%
                  (define/public (shoot left num) 
                    (- num 1))
                  (super-new)))
