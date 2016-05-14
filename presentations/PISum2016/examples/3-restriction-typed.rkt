#lang typed/racket

(define-type Cowboy (Class [draw (-> Any)]))
(define-type Gunslinger (Class [draw (-> String)]))

(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw) 42)
                  (super-new)))

(require/typed "2-untyped.rkt"
               [id (-> (Instance Cowboy) (Instance Gunslinger))]
               [di (-> (Instance Gunslinger) (Instance Cowboy))])

(define cowboy (make-object Cowboy%))
(define confused (di (id cowboy)))
(send confused draw)