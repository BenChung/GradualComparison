#lang racket
(require redex)

(define-language base
  (e ::= x (acc e f) (set e f e) (call e m e ...) (new C e ...) (cast t e))
  (t ::= ct dyn)
  (ct ::= (mt ...) C)
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
  (stp ::= (t t))
  (xi ::= (stp ...)))


(define-metafunction base
  append-token : m string -> m
  ((append-token m string) ,(string->symbol (string-append (symbol->string (term m)) (term string))))
  )


(define-metafunction base
  expand-once : c ... C -> t
  [(expand-once c_1 ... (class C (: f t) ... (m (x t_1) ... t_2 e) ...) c_2 ... C) ((f t) ... ((append-token f "!") t t) ... (m t_1 ... t_2) ...)])

(define-judgment-form base-subtyping
  #:mode (<= I I I I)
  #:contract (<= (c ...) xi t t)
  [------
   (<= (c ...) ((t_i1 t_i2) ... (t_1 t_2) (t_f1 t_f2) ...) t_1 t_2)]
  [(where stp_!_1 (t t))
   ------
   (<= (c ...) (stp_!_1 ...) t t)]
  [(where stp_!_1 (C_1 t_2))
   (<= (c ...) (stp ... (C_1 t_2)) (expand-once c ... C_1) t_2)
   -----
   (<= (c ...) ((name stp stp_!_1) ...) C_1 t_2)]
  [(where stp_!_1 (t_1 C_2))
   (<= (c ...) (stp ... (t_1 C_2)) t_1 (expand-once c ... C_2))
   -----
   (<= (c ...) ((name stp stp_!_1) ...) t_1 C_2)]
  [(where stp_!_1 (t ()))
   -----
   (<= (c ...) (stp_!_1 ...) t ())]
  [(where xi_p (stp ... (t_n1 t_n2))) 
   (<= (c ...) xi_p t_n1 (mt_e ...))
   (<= (c ...) xi_p t_1 t_i1) ...
   (<= (c ...) xi_p t_i2 t_2)
   ------
   (<= (c ...) ((name stp stp_!_1) ...) (name t_n1 (mt_1 ... (m t_1 ... t_2) mt_2 ...)) (name t_n2 ((m t_i1 ... t_i2) mt_e ...)))
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
   (--> (sigma_1 (c_1 ... (name ic (class C (: f t) ..._1 md ...)) c_2 ... (in-hole E (new C a ..._1))))
        (sigma_2 (c_1 ... ic c_2 ... (in-hole E a_1)))
        (where (sigma_2 a_1) (alloc sigma_1 a ... C C)))
   (--> (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
        (sigma_1 (c ... (in-hole E e_1)))
        (side-condition (redex-can-do? (lambda () (term (dispatch c ... sigma_1 v_1 m v_2 ...)))))
        (where e_1 (dispatch c ... sigma_1 v_1 m v_2 ...)))
   (--> (sigma_1 (c ... (in-hole E (call v_1 m v_2 ...))))
        err
        (side-condition (not (redex-can-do? (lambda () (term (dispatch c ... sigma_1 v_1 m v_2 ...)))))))
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
  [(expression-type (c ...) gamma e_1 C_1)
   (where (mt_1 ... (m t_a ... t_r) mt_2 ...) (expand-once c ... C_1))
   (expression-type (c ...) gamma e_2 t_a2) ...
   (<= (c ...) () t_a2 t_a) ...
   -------
   (expression-type (c ...) gamma (call e_1 m e_2 ..._1) t_r)]
  [(expression-type (c ...) gamma e_1 (mt_1 ... (m t_a ... t_r) mt_2 ...))
   (expression-type (c ...) gamma e_2 t_a2) ...
   (<= (c ...) () t_a2 t_a) ...
   -------
   (expression-type (c ...) gamma (call e_1 m e_2 ..._1) t_r)]
  [(expression-type c gamma e t_a) ...
   (<= c () t_a t_f) ...
   -------
   (expression-type (name c (c_1 ... (class C (: f t_f) ..._1 md ...) c_2 ...)) gamma (new C e ...) C)]
  [(expression-type (c ...) gamma e t_a) 
   -------
   (expression-type (c ...) gamma (cast t e) t)])

(test-equal (judgment-holds (expression-type (,fooclass) () (new foo) t) t) (term (foo)))
(test-equal (judgment-holds (expression-type (,fooclass) () (call (new foo) bar (new foo)) t) t) (term ()))
(test-equal (judgment-holds (expression-type (,fooclass) () (call (cast dyn (new foo)) bar (new foo)) t) t) (term (dyn)))
(test-equal (judgment-holds (expression-type (,foofooclass) () (call (new foo) bar (new foo)) t) t) (term (dyn)))
(test-equal (judgment-holds (expression-type (,fooclass) () (cast dyn (new foo)) t) t) (term (dyn)))

(define-judgment-form base
  #:mode (translate-program I O)
  #:contract (translate-program p p)
  [(translate-class (c ...) c c_1) ...
   (base-translate (c ...) () e e_1 t)
   ----
   (translate-program (c ... e) (c_1 ... e_1))])

(define-judgment-form base
  #:mode (translate-class I I O)
  #:contract (translate-class (c ...) c c)
  [(base-translate (c ...) ((x t_1) ...) e e_1 t_3) ...
   -----
   (translate-class (c ...)
                      (class C (name fd (: f t)) ... (name md (m (x t_1) ... t_2 e)) ...)
                      (class C fd ...
                        (m (x t_1) ... t_2 e_1) ...
                        (f t (acc this f)) ...
                        ((append-token f "!") (arg t) t (set this f arg)) ...
                        ((append-token m "*") (x dyn) ... dyn (cast dyn (call this m (cast t_1 x) ...))) ...))]
  )

(define-language L
  (e number
     (e ...)))
(define-metafunction L
   replace-with-0 : e -> e
   [(replace-with-0 (e ..._1)) ,(make-list (length (term (e ...))) 0)])

(define-judgment-form base
  #:mode (base-translate I I I O O)
  #:contract (base-translate (c ...) gamma e e t)
  [-------
   (base-translate (c ...) ((x_1 t_1) .... (x t) (x_2 t_2) ...) x x t)]
  [(base-translate (c ...) gamma e_1 e_3 dyn)
   (base-translate (c ...) gamma e_2 e_4 t) ...
   ------
   (base-translate (c ...) gamma (call e_1 m e_2 ..._1)
                   (call (cast ((m ,@(make-list (length (term (e_2 ...))) (term dyn)) dyn)) e_3) (append-token m "*") e_4 ...) dyn)]
  [(base-translate c gamma e_1 e_3 C)
   (where (mt_1 ... (m t_a ... t_r) mt_2 ...) (expand-once c C))
   (base-translate c gamma e_2 e_4 t_av) ...
   (<= c () t_av t_a) ...
   -----
   (base-translate (name c (c_i ...))
                   gamma (call e_1 m e_2 ..._1) (call e_3 m e_4 ...) t_r)]
  [(base-translate c gamma e e_1 t_a) ...
   (<= c () t_a t) ...
   ------
   (base-translate (name c (c_1 ... (class C (: f t) ... md ...) c_2 ...)) gamma (new C e ...) (new C e_1 ...) C)]
  [(base-translate (c ...) gamma e e_1 t_a)
   ------
   (base-translate (c ...) gamma (cast t e) (cast t e_1) t)]
  )

(define barclass (term (class bar (: baz dyn))))
(define dyncallclass (term (class bar (foo dyn (call (cast dyn (new bar)) foo)))))

(test-equal
 (judgment-holds (translate-class (,foofooclass) ,foofooclass c) c)
 (term ((class foo (bar (x foo) dyn x) (bar* (x dyn) dyn (cast dyn (call this bar (cast foo x))))))))

(test-equal
 (judgment-holds (translate-class (,barclass) ,barclass c) c)
 (term ((class bar (: baz dyn) (baz dyn (acc this baz)) (baz! (arg dyn) dyn (set this baz arg))))))

(test-equal
 (judgment-holds (translate-class (,dyncallclass) ,dyncallclass c) c)
 (term ((class bar (foo dyn (call (cast ((foo dyn)) (cast dyn (new bar))) foo*)) (foo* dyn (cast dyn (call this foo)))))))

(define (base-eval program)
  (car (apply-reduction-relation* b-> (term (() ,(car (judgment-holds (translate-program ,program p) p)))))))
#| Typed Racket |#

(define-metafunction base
  wrap : t e -> e
  ((wrap C e) (new (append-token C "*") e))
  ((wrap (mt ...) e) e) #| TODO |#
  ((wrap dyn e) e))

(define-metafunction base
  wrap-class : c -> c
  ((wrap-class (class C fd ... (m (x t_a) ... t e) ...))
   (class (append-token C "*") (: orig C)
     (m (x dyn) ... dyn (cast dyn (wrap t (call (acc this orig) m (wrap t_a (cast t_a x)) ...)))) ...)))

(define-extended-judgment-form base base-translate
  #:mode (racket-translate I I I O O)
  #:contract (racket-translate (c ...) gamma e e t)
  [(racket-translate (c ...) gamma e_1 e_3 dyn)
   (racket-translate (c ...) gamma e_2 e_4 t) ...
   ------
   (racket-translate (c ...) gamma (call e_1 m e_2 ...) (call e_3 m (wrap t e_4) ...) dyn)]
  [(racket-translate c gamma e_1 e_3 C)
   (where (mt_1 ... (m t_a ... t_r) mt_2 ...) (expand-once c C))
   (racket-translate c gamma e_2 e_4 t_av) ...
   (<= c () t_av t_a) ...
   -----
   (racket-translate (name c (c_i ...)) gamma (call e_1 m e_2 ..._1) (call e_3 m e_4 ...) t_r)]
  )

(define-judgment-form base
  #:mode (translate-racket-class I I O)
  #:contract (translate-racket-class (c ...) c c)
  [(expression-type (c ...) ((x ct_1) ...) e t) ...
   (<= (c ...) () t ct_2) ...
   -----
   (translate-racket-class (c ...)
                      (class C (name fd (: f ct)) ... (name md (m (x ct_1) ... ct_2 e)) ...)
                      (class C fd ...
                        (m (x ct_1) ... ct_2 e) ...
                        (f ct (acc this f)) ...
                        ((append-token f "!") (arg ct) ct (set this f arg)) ...))]
  [(racket-translate (c ...) ((x dyn) ...) e e_1 t) ...
   (<= (c ...) () t dyn) ...
   -----
   (translate-racket-class (c ...)
                      (class C (: f dyn) ... (m (x dyn) ... dyn e) ...)
                      (class C (: f dyn) ...
                        (m (x dyn) ... dyn e) ...
                        (f dyn (acc this f)) ...
                        ((append-token f "!") (arg dyn) dyn (set this f arg)) ...))]
  )

(define-judgment-form base
  #:mode (translate-racket-program I O)
  #:contract (translate-racket-program p p)
  [(translate-racket-class (c ...) c c_1) ...
   (racket-translate (c ...) () e e_1 t)
   ----
   (translate-racket-program (c ... e) (c_1 ... (wrap-class c_1) ... e_1))])


(define (rkt-eval program)
  (car (apply-reduction-relation* b-> (term (() ,(car (judgment-holds (translate-racket-program ,program p) p)))))))


(define foorktclass (term (class foo (bar (x dyn) dyn x))))
(test-equal (rkt-eval (term (,foorktclass (new foo)))) 1 #:equiv ctx-strip)

(define factprog (term (
                  (class foo (baz (inp foo) bar (new bar inp)))
                  (class bar)
                  )))

(test-results)