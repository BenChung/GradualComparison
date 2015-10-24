#lang racket
(require redex)
(require racket/match)
(require racket/sandbox)
; core language
; class C extends D { l1 : T, ..., m(x:t, ...):T { e} ...
; e ::= l | x.l(e,...) | const | if e e e | e + e | new C(e, ...) | e.l = e

(define-language L
  (clss (class label label ... (label t) ... (label (label t) ... t e ...)))
  (p (program clss ...))
  (e
   (lookup e label)
   (call e label e ...)
   string
   integer
   (if e e e)
   (oplus e e)
   (new label (e ...) )
   (assign e label e))
  (label string)
  (t
   (tany)
   label
   (tstr)
   (tint)
   (! label))
)

(redex-check L p
             (term p)
             #:print? #t #:attempts 10)

(define evaluator (make-module-evaluator "#lang typed/racket"))
(evaluator '(begin (: x Integer) (define x "foo") x))
(match (term (lookup 2 "foo"))
  [`(lookup ,x ,name) `(,x ,name)]
  [`(call ,e1 ,name ,e2 ...) `(,name)]
  [`(if ,e1 ,e2 ,e3) `(,e1 ,e2 ,e3)]
  [`(oplus ,e1 ,e2) `(,e1 ,e2)]
  [`(new ,name (,arg ...)) `(,name ,arg ...)]
  [`(assign ,e1 ,name ,e2) `(,e1 ,name ,e2)]
  [`cons `(,cons)]
  )

(display-to-file (quasiquote ((foo 1) 3 1 2)) "test.rkt" #:exists `replace)