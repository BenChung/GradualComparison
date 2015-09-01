#lang typed/racket

(define-type Inner (Class (field (i Any)) [set (Any -> Void)] [get (-> Any)]))
(: Inner% Inner)
(define Inner% (class object%
                 (super-new)
                 (field (i 0))
                 (define/public (set v) (set! i v))
                 (define/public (get) i)
  ))


(define-type Main (Class (field (i (Instance Inner))) [main (-> Any)]))
(: Main% Main)
(define Main% (class object%
                (super-new)
                (field (i (make-object Inner%)))
                (define/public (main)
                  (set! i (make-object Inner%))
                  (send i set 1)
                  (send i set "test")
                  (send i get))
  ))


(define test (make-object Main%))
(send test main)

