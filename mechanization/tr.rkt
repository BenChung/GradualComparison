#lang racket
(require racket/set)
(require redex)
(require redex/reduction-semantics)

(define-language L
  (e x
     v
     (send e m e ...)
     (new C e ...)
     (cast t e)
     (get e f)
     (set e f e))
  (c (class C fd ... md ...))
  (mt (m t ... t))
  (to beh mono conc)
  (t anyt
     (to mt ...))
  (fd (f t))
  (md (m (x t) ... t e))
  (C f m x ::= variable-not-otherwise-mentioned)
  (Γ · (x : t Γ))
  (p (c ... e σ) err)
  (a number)
  (v a)
  (P E)
  (σ · (number ↦ {number ... C} σ))
  (E (send E m e ...)
     (send v m v ... E e ...)
     (new C v ... E e ...)
     (cast t E)
     (get E f)
     (set E f e)
     (set v f E)
     hole)
  #:binding-forms (m (x t_1) ... t_2 e #:refers-to (shadow x ...)))

(define-metafunction L
  bound-addrs : σ -> (number ...)
  [(bound-addrs (a ↦ {_ ... _} σ)) (a a_1 ...) (where (a_1 ...) (bound-addrs σ))]
  [(bound-addrs ·) ()])
(test-equal (term (bound-addrs (0 ↦ {te} (2 ↦ {te} ·)))) (term (0 2)))

(define (find-hole list)
  (set-first (set-subtract (list->set (stream->list (in-range 0 (+ 1 (length list))))) (list->set list))))


(define-metafunction L
  alloc : σ a ... C -> (a σ)
  [(alloc σ a ... C) (a_1 (a_1 ↦ {a ... C} σ)) (where a_1 ,(find-hole (term (bound-addrs σ))))])

(define-metafunction L
  lookup-heap : σ a -> (a ... C)
  [(lookup-heap (a ↦ {a_1 ... C} σ) a) (a_1 ... C)]
  [(lookup-heap (a_!_1 ↦ (a_1 ... C) σ) (name a a_!_1)) (lookup-heap σ a)])

(define-metafunction L
  update-heap : σ a (a ... C) -> σ
  [(update-heap (a ↦ {a_1 ... C} σ) a (a_2 ... C_1)) (a ↦ (a_2 ... C_1) σ)]
  [(update-heap ((name a_3 a_!_1) ↦ (a_1 ... C) σ) (name a a_!_1) (a_2 ... C_1)) (a_3 ↦ (a_1 ... C) (update-heap σ a (a_2 ... C_1)))])

(define-metafunction L
  subst-mult : x ... v ... e -> e
  [(subst-mult x_1 x_2 ... v_1 v_2 ... e) (subst-mult x_2 ... v_2 ... (substitute e x_1 v_1))]
  [(subst-mult e) e])

(define-metafunction L
  dispatch : σ a m v ... c ... -> e
  [(dispatch σ a m v ..._1 c_1 ... (class C fd ... md_1 ... (m (x t_1) ..._1 t_2 e) md_2 ...) c_2 ...)
   (subst-mult this x ... a v ... e) (where (a_1 ... C) (lookup-heap σ a))])

(define-metafunction L
  do-cast : a t σ c ... -> (e σ c ...) or err
  [(do-cast a (beh mt ...) σ c ...) (a σ c ...)]
  [(do-cast a (mono mt ...) σ c ...) (a σ c ...)]
  [(do-cast a (conc mt ...) σ c ...) (a σ c ...)])

(define red
  (reduction-relation L
                      #:domain p
                      (--> (c_1 ... (name c (class C fd ..._1 md ...)) c_2 ... (in-hole P (new C v ..._1)) σ_1)
                           (c_1 ... c c_2 ... (in-hole P a) σ_2)
                           (where (a σ_2) (alloc σ_1 v ... C)))
                      (--> (c ... (in-hole P (send a_1 m a_2 ...)) σ)
                           (c ... (in-hole P e) σ)
                           (where e (dispatch σ a_1 m a_2 ... c ...)))
                      (--> (c_1 ... (name c (class C fd_1 ..._1 (f t) fd_3 ..._3)) c_2 ... (in-hole P (get a f)) σ)
                           (c_1 ... c c_2 ... (in-hole P a_2) σ)
                           (where (a_1 ..._1 a_2 a_3 ..._3 C) (lookup-heap σ a)))
                      (--> (c_1 ... (name c (class C fd_1 ..._1 (f t) fd_3 ..._2)) c_2 ... (in-hole P (set a_1 f a_2)) σ_1)
                           (c_1 ... c c_2 ... (in-hole P a_2) σ_2)
                           (where (a_3 ..._1 a_4 a_5 ..._2 C) (lookup-heap σ_1 a_1))
                           (where σ_2 (update-heap σ_1 a_1 (a_3 ... a_2 a_5 ... C))))
                      (--> (c_1 ... (in-hole P (cast t a)) σ_1)
                           (c_2 ... (in-hole P e) σ_2)
                           (where (e σ_1 c_2 ...) (do-cast a t σ_1 c_1 ...)))
                      (--> (c_1 ... (in-hole P (cast t a)) σ_1)
                           err
                           (where err (do-cast a t σ_1 c_1 ...)))))

(test-equal (apply-reduction-relation* red (term ((class C (f anyt)) (class D) (new C (new C (new D))) ·)))
            '(((class C (f anyt)) (class D) 2 (2 ↦ (1 C) (1 ↦ (0 C) (0 ↦ (D) ·))))))
(test-equal (apply-reduction-relation* red (term ((class C (m (x anyt) anyt (new C))) (send (new C) m (new C)) ·)))
            '(((class C (m (x anyt) anyt (new C))) 2 (2 ↦ (C) (1 ↦ (C) (0 ↦ (C) ·))))))
(test-equal (apply-reduction-relation* red (term ((class C (f anyt)) (class D) (get (new C (new D)) f) ·)))
            '(((class C (f anyt)) (class D) 0 (1 ↦ (0 C) (0 ↦ (D) ·)))))
(test-equal (apply-reduction-relation* red (term ((class C (f anyt)) (class D) (set (new C (new D)) f (new D)) ·)))
            '(((class C (f anyt)) (class D) 2 (2 ↦ (D) (1 ↦ (2 C) (0 ↦ (D) ·))))))

(define-metafunction L
  lookup-env : Γ x -> t
  [(lookup-env (x : t Γ) x) t]
  [(lookup-env (x_!_1 : t Γ) (name x x_!_1)) (lookup-env Γ x)])

(define-metafunction L
  get-function : m t -> (t ... t)
  [(get-function m (_ (m_1 t_1 ... t_2) ... (m t_5 ... t_6) (m_2 t_3 ... t_4) ...)) (t_5 ... t_6)])

(define-metafunction L
  append-symbol : x x -> x
  [(append-symbol x_1 x_2) ,(string->symbol (string-append (symbol->string (term x_1)) (symbol->string (term x_2))))])

(define-metafunction L
  class-to-type : c -> t
  [(class-to-type (class C fd ... (m (x t_1) ... t_2 e) ...)) (beh (m t_1 ... t_2) ...)])

(define-metafunction L
   repeat-times : (e ...) t -> (t ...)
   [(repeat-times (e ...) t_1) ,(make-list (length (term (e ...))) (term t_1))])

(define-judgment-form L
  #:mode (<: I I)
  #:contract (<: t t)
  [--------
   (<: t t)]
  [--------
   (<: (to mt ...) (to))]
  [(<: t_3 t_1) ...
   (<: t_2 t_4)
   (<: (to mt_1 ... mt_2 ...) (to mt_3 ...))
   -------
   (<: (to mt_1 ... (m t_1 ... t_2) mt_2 ...) (to (m t_3 ... t_4) mt_3 ...))])

(define-judgment-form L
  #:mode (syntype I I I O O)
  #:contract (syntype (c ...) Γ e e t)
  [(where t (lookup-env Γ x))
   -------  "A1"
   (syntype _ Γ x x t)]
  [(syntype (c ...) Γ e e_1 t_1)
   (where (t) (get-function f t_1))
   -------  "A2"
   (syntype (c ...) Γ (get e f) (send e_1 f) t)]
  [(syntype (c ...) Γ e_1 e_3 t_1)
   (where (t t) (get-function (append-symbol f !) t_1))
   (anatype (c ...) Γ e_2 t e_4)
   ------- "A3"
   (syntype (c ...) Γ (set e_1 f e_2) (send e_3 (append-symbol f !) e_4) t)]
  [(syntype (c ...) Γ e_1 e_3 t_1)
   (where (to mt ...) t_1)
   (where (t_2 ..._1 t_3) (get-function m t_1))
   (anatype (c ...) Γ e_2 t_2 e_4) ...
   ----- "A4-Recv"
   (syntype (c ...) Γ (send e_1 m e_2 ..._1) (send e_3 m e_4 ...) t_3)]
  [(syntype (c ...) Γ e_1 e_3 t_1)
   (where anyt t_1)
   (anatype (c ...) Γ e_2 anyt e_4) ...
   (where (t_a ...) (repeat-times (e_2 ...) anyt))
   ----- "A4-Dyn"
   (syntype (c ...) Γ (send e_1 m e_2 ..._1) (send (cast (beh ((append-symbol m u) t_a ... anyt)) e_3) m e_4 ...) anyt)]
  [(anatype (c_1 ... c c_2 ...) Γ e_1 t e_2) ...
   (where t_2 (class-to-type c))
   ----- "A5"
   (syntype (c_1 ... (name c (class C (f t) ..._1 md ...)) c_2 ...) Γ (new C e_1 ..._1) (new C e_2 ...) t_2)]
  )

(define-judgment-form L
  #:mode (anatype I I I I O)
  #:contract (anatype (c ...) Γ e t e)
  [(syntype (c ...) Γ e_1 e_2 t_2)
   (<: t_2 t_1)
   ----- "AASC1"
   (anatype (c ...) Γ e_1 t_1 e_2)]
  [(syntype (c ...) Γ e_1 e_2 anyt)
   ---- "AASC2"
   (anatype (c ...) Γ e_1 (to mt ...) (cast (to mt ...) e_2))]
  [(syntype (c ...) Γ e_1 e_2 (to mt ...))
   ---- "AASC3"
   (anatype (c ...) e_1 Γ anyt (cast anyt e_2))])

(test-equal (judgment-holds (syntype () (x : (beh (m anyt anyt)) ·) x e t) t)
            '((beh (m anyt anyt))))
(test-equal (judgment-holds (syntype () (x : (beh (m anyt)) ·) (get x m) e t) t)
            '(anyt))
(test-equal (judgment-holds (syntype () (x : (beh (m! anyt anyt)) (y : anyt ·)) (set x m y) e t) t)
            '(anyt))
(test-equal (judgment-holds (syntype () (x : (beh (m anyt anyt)) (y : anyt ·)) (send x m y) e t) t)
            '(anyt))
(test-equal (judgment-holds (syntype () (x : anyt (y : anyt ·)) (send x m y) e t) t)
            '(anyt))
(test-equal (judgment-holds (syntype ((class C (f anyt) (m (x anyt) anyt x))) (x : anyt ·) (new C x) e t) t)
            '((beh (m anyt anyt))))
