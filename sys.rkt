#lang racket
(require redex)

(define-language base
  (e ::= x (acc e f) (set e f e) (call e m e ...) (new C e ...) (cast t e))
  (t ::= any (mt ...) C)
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


(define-extended-language base-subtyping base
  (xi ::= ((t t) ...)))

(define-metafunction base
  expand-once : c ... C -> t
  [(expand-once c_1 ... (class C fd ... (m (x t_1) ... t_2 e) ...) c_2 ... C) ((m t_1 ... t_2) ...)])

(define-judgment-form base-subtyping
  #:mode (<= I I I I)
  #:contract (<= (c ...) xi t t)
  [------
   (<= (c ...) xi t t)]
  [------
   (<= (c ...) ((t_i1 t_i2) ... (t_1 t_2) (t_f1 t_f2) ...) t_1 t_2)]
  [(where C_1 t_1)
   (where C_2 t_2)
   (where ((t_i1 t_i2) ...) xi)
   (<= (c ...) ((t_i1 t_i2) ... (C_1 C_2)) (expand-once c ... C_1) (expand-once c ... C_2))
   -----
   (<= (c ...) (name xi ((t_!_1 t_!_2) ...)) (name t_1 t_!_1) (name t_2 t_!_2))]
  [-----
   (<= (c ...) xi t ())]
  [(where xi_p ((t_xi1 t_xi2) ... (t_n1 t_n2))) 
   (<= (c ...) xi_p t_n1 (mt_e ...))
   (<= (c ...) xi_p t_1 t_i1) ...
   (<= (c ...) xi_p t_i2 t_2)
   ------
   (<= (c ...) ((t_xi1 t_xi2) ...) (name t_n1 (mt_1 ... (m t_1 ... t_2) mt_2 ...)) (name t_n2 ((m t_i1 ... t_i2) mt_e ...)))
   ]
  )

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
             a_v ..._1) (subst-multi e (this x ...) (a a_v ...))
             ])

(define-metafunction base-dynamics
  read-helper : c ... sigma v f -> v
  [(read-helper
    c_1 ... (class C fd_1 ..._1 (: f t_1) fd_2 ..._2 md ...) c_2 ...
    (memloc_1 ... (a (a_1 ..._1 a_v a_2 ..._2) t_2 C) memloc_2 ...)
    a f)
   a_v])

(define-metafunction base-dynamics
  write-helper : c ... sigma v f v -> sigma
  [(write-helper
    c_1 ... (class C fd_1 ..._1 (: f t_1) fd_2 ..._2 md ...) c_2 ...
    (memloc_1 ... (a (a_1 ..._1 a_v a_2 ..._2) t_2 C) memloc_2 ...)
    a f a_new)
   (memloc_1 ... (a (a_1 ... a_new a_2 ...) t_2 C) memloc_2 ...)])

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
   (--> (sigma_1 (c ... (in-hole E (set v_1 f v_2))))
        (sigma_2 (c ... (in-hole E v_2)))
        (where sigma_2 (write-helper c ... sigma_1 v_1 f v_2)))
   (--> (sigma_1 (c ... (in-hole E (cast any v_1))))
        (sigma_1 (c ... (in-hole E v_1))))
   (--> ((memloc_1 ... (a (a_2 ...) t_2 C) memloc_2 ...) (c ... (in-hole E (cast t_1 a))))
        (sigma_1 (c ... (in-hole E a)))
        (judgment-holds (<= (c ...) () t_2 t_1)))
  ))

(define fooclass (term (class foo (bar (x any) any x))))
(define foofooclass (term (class foo (bar (x foo) any x))))

(define testprog (term (,fooclass (new foo))))
(define testprog2 (term ((class foo (bar (x any) any x)) (call (new foo) bar 1))))
(define testprog3 (term ((class foo (: bar any)) (class bar) (acc (new foo (new bar)) bar))))
(define testprog4 (term ((class foo (: bar any)) (class bar) (set (new foo (new bar)) bar (new bar)))))
(define testprog5 (term (
                         (class foo
                           )
                         (class bar) (set (new foo (new bar)) bar (new bar)))))