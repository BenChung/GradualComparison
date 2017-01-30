#lang typed/racket

(define-type C (Class [n ((Instance C) -> (Instance C))]))
(define-type D (Class [o ((Instance D) -> (Instance D))]))

(define-type I (Class [m ((Instance C) -> (Instance C))]))
(define-type J (Class [m ((Instance D) -> (Instance D))]))
(define-type E (Class
                (init [fi (Instance I)])
                (init [gi (Instance J)])
                (field [f (Instance I)])
                (field [g (Instance J)])))


(: E% E)
(define E% (class object%
             (super-new)
             (init [fi : (Instance I)]
                   [gi : (Instance J)])
             (field (f fi)
                    (g gi))))

(provide E%)