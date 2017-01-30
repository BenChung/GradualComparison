#lang racket

(require "litmus3t.rkt")

(define A% (class object%
             (super-new)
             (define/public (m x) this)))
(define T% (class object%
              (super-new)
              (define/public (t x)
                (get-field f (make-object E% x x)))))
(send (make-object T%) t (make-object A%))

#|(define-type A (Class [m (Any -> Any)]))
(define-type TU (Class [t (Any -> Any)]))|#