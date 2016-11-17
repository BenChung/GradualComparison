#lang typed/racket

(define-type Fact (Class [main (-> Any)] [mul (-> Integer Integer Integer)] [fact (-> Any Any)]))
(: Fact% Fact)
(define Fact% (class object%
             (super-new)
             (define/public (main) (send this fact 5))
             (define/public (mul i j) (if (= i 0) 0 (+ j (mul (- i 1) j))))
             (define/public (fact i)
               (if (= (cast i Integer) 0)
                   1
                   (mul (cast i Integer) (cast (fact (- (cast i Integer) 1)) Integer))))
  ))


(define test (make-object Fact%))
(send test main)