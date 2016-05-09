#lang racket
(require redex)

(define-language base
  (e ::= x (acc e f) (set e f e) (call e m e ...) (new C e ...) (cast t e))
  (t ::= dyn (mt ...) C)
  (mt ::= (m t ... t))
  (fd ::= (: f t))
  (md ::= (m (x t) ... t e))
  (c ::= (class C fd ... md ...))
  (p ::= (c ... e))
  (gamma ::= ((x t) ...))
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
  [(where ((t_i1 t_i2) ...) xi)
   (<= (c ...) ((t_i1 t_i2) ... (C_1 C_2)) (expand-once c ... C_1) (expand-once c ... C_2))
   -----
   (<= (c ...) (name xi ((C_!_1 C_!_2) ...)) (name C_1 C_!_1) (name C_2 C_!_2))]
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


(define fooclass (term (class foo (bar (x dyn) dyn x))))
(test-equal (judgment-holds (<= (,fooclass) () foo foo)) #t)
(test-equal (judgment-holds (<= (,fooclass) () foo dyn)) #f)
(test-equal (judgment-holds (<= (,fooclass) () dyn dyn)) #t)
(test-equal (judgment-holds (<= (,fooclass) () dyn foo)) #f)

(define foofooclass (term (class foo (bar (x foo) dyn x))))
(test-equal (judgment-holds (<= (,foofooclass) () foo foo)) #t)

(define foodynclass (term (class food (bar (x dyn) dyn x))))
(test-equal (judgment-holds (<= (,foofooclass ,foodynclass) () foo food)) #f)
(test-equal (judgment-holds (<= (,foofooclass ,foodynclass) () food foo)) #f)


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

(define (redex-can-do? redex-matcher)
  (with-handlers
      ([exn:fail:redex? (lambda x #f)])
    (begin
      (redex-matcher)
      #t)))

(define b->
  (reduction-relation
   base-dynamics
   #:domain res
   (--> (sigma (c ... (in-hole E err))) err)
   (--> (sigma_1 (c_1 ... (name ic (class C (: f t) ..._1 md ...)) c_2 ... (in-hole E (new C a ..._1))))
        (sigma_2 (c_1 ... ic c_2 ... (in-hole E a_1)))
        (where (sigma_2 a_1) (alloc sigma_1 a ... C C)))
   (--> (side-condition (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
                        (redex-can-do? (lambda () (term (dispatch c ... sigma_1 v_1 m v_2 ...)))))
        (sigma_1 (c ... (in-hole E e_1)))
        (where e_1 (dispatch c ... sigma_1 v_1 m v_2 ...)))
   (--> (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
         err
         (side-condition (not (redex-can-do?
                          ))))
   (--> (sigma_1 (c ... (in-hole E (acc v_1 f))))
        (sigma_1 (c ... (in-hole E v_2)))
        (where v_2 (read-helper c ... sigma_1 v_1 f)))
   (--> (sigma_1 (c ... (in-hole E (set v_1 f v_2))))
        (sigma_2 (c ... (in-hole E v_2)))
        (where sigma_2 (write-helper c ... sigma_1 v_1 f v_2)))
   (--> (sigma_1 (c ... (in-hole E (cast dyn v_1))))
        (sigma_1 (c ... (in-hole E v_1))))
   (--> ((name sigma_1 (memloc_1 ... (a (a_2 ...) t_2 C) memloc_2 ...)) (c ... (in-hole E (cast t_1 a))))
        (sigma_1 (c ... (in-hole E a)))
        (judgment-holds (<= (c ...) () t_2 t_1)))
   (--> ((memloc_1 ... (a (a_2 ...) t_2 C) memloc_2 ...) (c ... (in-hole E (cast t_1 a))))
        err
        (side-condition (not (judgment-holds (<= (c ...) () t_2 t_1)))))
  ))

(define-metafunction base-dynamics
  [(strip-context e) e]
  [(strip-context (sigma (c ... e))) e]
  [(strip-context (sigma (c ... err))) err]
  [(strip-context err) err])
(define (ctx-strip a b) (alpha-equivalent? base-dynamics (term (strip-context ,a)) (term (strip-context ,b))))

(define testprog (term (,fooclass (new foo))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog)) 1)

(define testprog2 (term ((class foo (bar (x dyn) dyn x)) (call (new foo) bar 1))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog2)) 1)

(define testprog21 (term ((class foo (bar (x dyn) dyn x)) (call (new foo) baz 1))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog21)) (term err))

(define testprog3 (term ((class foo (: bar dyn)) (class bar) (acc (new foo (new bar)) bar))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog3)) 1)

(define testprog4 (term ((class foo (: bar dyn)) (class bar) (set (new foo (new bar)) bar (new bar)))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog4)) 3)

(define testprog5 (term (
                         (class foo)
                         (class bar)
                         (cast foo (new bar)))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog5)) 1)

(define testprog51 (term (
                         (class foo (m1 dyn (new bar)))
                         (class bar)
                         (cast foo (new bar)))))
(test-->> b-> #:equiv ctx-strip (term (() ,testprog51)) (term err))

(define-judgment-form base
  #:mode (program-type I)
  #:contract (program-type p)
  [(method-type (c_s c ...) md) ...
   (expression-type (c_s c ...) () e t)
   -------
   (program-type ((name c_s (class C fd ... md ...)) c ... e))])

(define-judgment-form base
  #:mode (method-type I I)
  #:contract (method-type (c ...) md)
  [(expression-type (c ...) ((x t) ...) e t_3)
   (<= (c ...) () t_3 t_2)
   -------
   (method-type (c ...) (m (x t) ... t_2 e))])

(define-judgment-form base
  #:mode (expression-type I I I O)
  #:contract (expression-type (c ...) gamma e t)
  [-------
   (expression-type (c ...) ((x_1 t_1) ... (x t) (x_2 t_2) ...) x t)]
  [(expression-type (c ...) gamma e_1 t_1)
   (<= (c ...) () dyn t_1)
   (expression-type (c ...) gamma e_2 t_2) ...
   -------
   (expression-type (c ...) gamma (call e_1 m e_2 ...) dyn)]
  [(expression-type c gamma e_1 C_1)
   (expression-type c gamma e_2 t_a2) ...
   (<= c () t_a2 t_a) ...
   -------
   (expression-type (name c (c_1 ... (class C_1 fd ... md_1 ... (m (x t_a) ..._1 t_r e_3) md_2 ...) c_2 ...))
                    gamma (call e_1 m e_2 ..._1) t_r)]
  [(expression-type (c ...) gamma e_1 (mt_1 ... (m t_a ... t_r) mt_2 ...))
   (expression-type (c ...) gamma e_2 t_a2) ...
   (<= (c ...) () t_a2 t_a) ...
   -------
   (expression-type (c ...) gamma (call e_1 m e_2 ..._1) t_r)]
  [(expression-type c gamma e t_a) ...
   (<= c () t_a t_f) ...
   -------
   (expression-type (name c (c_1 ... (class C (: f t_f) ..._1 md ...) c_2 ...)) gamma (new C e ...) C)])

(test-results)