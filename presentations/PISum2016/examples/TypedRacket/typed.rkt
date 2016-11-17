#lang typed/racket

(define-type Gun (Class [shoot (Integer -> Integer)]))
(: Gun% Gun)
(define Gun% (class object%
                  (define/public (shoot num) 
                    (- num 1))
                  (super-new)))

(define-type Cowboy (Class [draw ((Instance Gun) -> Integer)]))
(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw g) 
                    (send g shoot 8))
                  (super-new)))
