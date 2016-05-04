#lang racket
(require redex)

(define-language base
  (e ::= x (acc e f) (set e f e) (call e m e ...) (new C e ...) (cast t e))
  (t ::= any (mt ...))
  (mt ::= (m t ... t))
  (fd ::= (: f t))
  (md ::= (m (x t) ... t e))
  (c ::= (class C fd ... md ...))
  (p ::= (c ... e))
  (x f C m ::= variable-not-otherwise-mentioned)
  )

(define-extended-language base-dynamics base
  (e ::= v x (acc e f) (set e f e) (call e m e ...) (new C e ...) (cast t e))
  (E ::= hole (acc E f) (set E f e) (set v f E) (call E m e ....) (call v m v ... E e ...) (new C v ... E e ...) (cast t E))
  (v ::= a)
  (a ::= number)
  (memloc ::= (a (a ...) t C))
  (sigma ::= (memloc ...))
  (res ::= (sigma p) err))



(define-metafunction base-dynamics
  get-open : sigma -> a
  [(get-open ((a_1 (a_2 ...) t C) ...)) ,(+ (apply max (cons 0 (term (a_1 ...)))) 1)]
  )

(define-metafunction base-dynamics
  alloc : sigma a ... t C -> (sigma a)
  [(alloc (memloc ...) a ... t C) ((memloc ... (a_out (a ...) t C)) a_out) (where a_out (get-open (memloc ...)))]
  )

(define-metafunction base-dynamics
  subst-exn : e x v -> e
  [(subst-exn x x v) v]
  [(subst-exn (name x_1 x_!_1) x_!_2 v) x_1]
  [(subst-exn v x v_1) v]
  [(subst-exn (acc e f) x v) (acc (subst-exn e x v) f)]
  [(subst-exn (set e_1 f e_2) x v) (set (subst-exn e_1 x v) f (subst-exn e_2 x v))]
  [(subst-exn (call e m e_1 ...) x v) (call (subst-exn e x v) m (subst-exn e_1 x v) ...)]
  [(subst-exn (new C e ...) x v) (new C (subst-exn e x v) ...)]
  [(subst-exn (cast t e) x v) (cast t (subst-exn e x v))]
  )

(define-metafunction base-dynamics
  subst-multi : e (x ...) (v ...) -> e
  [(subst-multi e_1 (x x_2 ...) (v v_2 ...)) (subst-multi (subst-exn e_1 x v) (x_2 ...) (v_2 ...))]
  [(subst-multi e_1 () ()) e_1])

(define-metafunction base-dynamics
  dispatch : c ... sigma a m a ... -> e
  [(dispatch c_1 ... (name ic (class C fd ... md_1 ... (m (x t_1) ..._1 t_2 e) md_2 ...)) c_2 ...
             (memloc_1 ... (a (a_1 ...) t C) memloc_2 ...)
             a
             m
             a_v ..._1) (subst-multi e (x ...) (a_v ...))
             ])

(define-metafunction base-dynamics
  read-helper : c ... sigma v f -> v
  [(read-helper
    c_1 ... (class C fd_1 ..._1 (: f t_1) fd_2 ..._2 md ...) c_2 ...
    (memloc_1 ... (a (a_1 ..._1 a_v a_2 ..._2) t_2 C) memloc_2 ...)
    a f)
   a_v])

(define b->
  (reduction-relation
   base-dynamics
   #:domain res
   (--> (sigma_1 (c_1 ... (name ic (class C (: f t) ..._1 md ...)) c_2 ... (in-hole E (new C a ..._1))))
        (sigma_2 (c_1 ... ic c_2 ... (in-hole E a_1)))
        (where (sigma_2 a_1) (alloc sigma_1 a ... C C)))
   (--> (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
        (sigma_1 (c ... (in-hole E e_1)))
        (where e_1 (dispatch c ... sigma_1 v_1 m v_2 ...)))
   (--> (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
        err)
   (--> (sigma_1 (c ... (in-hole E (acc v_1 f))))
        (sigma_1 (c ... (in-hole E v_2)))
        (where v_2 (read-helper c ... sigma_1 v_1 f)))
  ))

(define testprog (term ((class foo (bar (x any) any x)) (new foo))))
(define testprog2 (term ((class foo (bar (x any) any x)) (call (new foo) bar 1))))
(define testprog3 (term ((class foo (: bar any)) (class bar) (acc (new foo (new bar)) bar))))