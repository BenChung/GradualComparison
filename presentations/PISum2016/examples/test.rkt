#lang typed/racket

(define-type Gun (Class [shoot (-> Integer Integer)]))
(: Gun% Gun)
(define Gun% (class object%
                  (define/public (shoot num)
                    (- num 1))
                  (super-new)))


(define-type Pencil (Class [draw (-> Integer Integer)]))
(: Pencil% Pencil)
(define Pencil% (class object%
                  (define/public (draw num)
                    (- num 1))
                  (super-new)))


(define-type Cowboy (Class [draw (-> (Instance Gun) Integer)]))

(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw g)
                    (send g shoot 6))
                  (super-new)))

(define-type Painter (Class [draw (-> String  String)]))

(: Painter% Painter)
(define Painter% (class object%
                   (define/public (draw color)
                            (string-join (list "Pretty" color "picture")))
                   (super-new)))


(define painter (make-object Painter%))


(send painter draw "blue")


(: test (-> (Instance Cowboy) (Instance Gun) Integer))
(define (test subj obj)
   (send subj draw obj))

(require/typed "2-untyped.rkt"
               [id (-> (Instance Cowboy) (Instance Painter))]
               [di (-> (Instance Painter) (Instance Cowboy))])


(test (di painter) (make-object Gun%))