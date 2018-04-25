#lang racket
(require racket/class)
(provide id)
(define (id x) x)
(define E% (class object%
             (define/public (foo) "string")
             (super-new)
             ))

