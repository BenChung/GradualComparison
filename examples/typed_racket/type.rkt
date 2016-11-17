#lang typed/racket

(define-type Cowboy (Class [draw (Integer -> Integer)]))
(define-type Painter (Class [draw (String -> String)]))

(: Cowboy% Cowboy)
(define Cowboy% (class object%
                  (define/public (draw it) 
                    (- it 1))
                  (super-new)))

(: Painter% Painter)
(define Painter% (class object%
                   (define/public (draw it)
                            (string-join (list "Pretty" it "picture")))
                   (super-new)))

(require/typed "untyped.rkt"
               [id (-> (Instance Painter) (Instance Cowboy))])

(define painter (make-object Painter%))


(: test (-> (Instance Cowboy) Integer Integer))
(define (test subj obj)
  (begin  (print "Testing")
   (send subj draw obj)))

(send painter draw "blue")
(test (id painter) 8)