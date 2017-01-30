#lang typed/racket
(define-type C (Class [n ((Instance C) -> (Instance C))]))
(define-type D (Class [o ((Instance D) -> (Instance D))]))

(define-type A (Class
                (init [fi Any])
                (field [f Any])
                [m ((Instance A)-> (Instance A))]))
(define-type I (Class
                (init [fi (Instance D)])
                (field [f (Instance D)])
                [m ((Instance I) -> (Instance I))]))

(define-type T (Class [s ((Instance I) -> (Instance I))]
                      [t (Any -> Any)]))


(require/typed "uthelper.rkt"
               [id (-> Any (Instance I))])

(: C% C)
(define C% (class object%
                (super-new)
                (define/public (n x)
                  this)))
(: D% D)
(define D% (class object%
                (super-new)
                (define/public (o x)
                  this)))

(: A% A)
(define A% (class object%
             (super-new)
             (init [fi : Any])
             (field [f fi])
             (define/public (m x)
               (define res (make-object A% (make-object C%)))
               (set-field! f this res)
               res)))
(: I% I)
(define I% (class object%
             (super-new)
             (init [fi : (Instance D)])
             (field [f fi])
             (define/public (m x)
               this)))

(: T% T)
(define T% (class object%
             (super-new)
             (define/public (s x)
               (send x m x))
             (define/public (t x)
               (send this s (id x)))))

(send (make-object T%) t (make-object A% (make-object D%)))