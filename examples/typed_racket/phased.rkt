#lang typed/racket

(define-type Gun (Class [fire (-> Integer)]))

(define-type Cowboy (Class [draw (-> (Instance Gun) Any)]))
(define-type Gunslinger (Class [draw (-> (Instance Gun) Integer Any)]))

(: Gun% Gun)
(define Gun% (class object%
               (define/public (fire) 1)
               (super-new)))

(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw it) 
                    (send it fire))
                  (super-new)))

(require/typed "untyped.rkt"
               [id (-> (Instance Cowboy) (Instance Gunslinger))]
               [id2 (-> (Instance Gunslinger) Any)])

(define gun (make-object Gun%))

(define cowboy (make-object Cowboy%))
(define gunslinger (id cowboy))
(send gunslinger draw gun)


