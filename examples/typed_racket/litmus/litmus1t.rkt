#lang typed/racket

(define-type A (Class [m ((Instance A)-> (Instance A))]))
(define-type I (Class [n ((Instance I) -> (Instance I))]))
(define-type T (Class [s ((Instance I) -> (Instance T))]
                      [t (Any -> Any)]))


(require/typed "uthelper.rkt"
               [id (-> Any (Instance I))])


(: A% A)
(define A% (class object%
                (super-new)
                (define/public (m x)
                  this)))
(: I% I)
(define I% (class object%
             (super-new)
             (define/public (n x)
               this)))

(: T% T)
(define T% (class object%
             (super-new)
             (define/public (s x)
               this)
             (define/public (t x)
               (send this s (id x)))))

(send (make-object T%) t (make-object A%))