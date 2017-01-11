#lang racket
(require racket/set)
(require redex)
(require redex/reduction-semantics)

(define-language KafKa
  (e x
     v
     (call e m e)
     (call e f e)
     (call e f)
     (dcall e m e)
     (new C e ...)
     (subcast t e)
     (namcast t e)
     (behcast t e)
     (moncast t e))
  (k (class C fd ... md ...))
  (mt (m t t) (f t t) (f t))
  (t anyt C)
  (fd (f t))
  (md (m (x t) t e) (f (x t) t e) (f t e))
  (m (variable-prefix m))
  (f (variable-prefix f) that)
  (n m f)
  (C D x ::= variable-not-otherwise-mentioned)
  (Γ · (x : t Γ))
  (K (k ...))
  (p (e K))
  (P (e K σ))
  (a number)
  (v a)
  (mts (mt ...))
  (σa (a ↦ {a ... C}))
  (σ (σa ...))
  (E (call E m e)
     (call E f e)
     (call E f)
     (call v m E)
     (call v f E)
     (dcall E m e)
     (dcall v m E)
     (new C v ... E e ...)
     (subcast t E)
     (namcast t E)
     (behcast t E)
     (moncast t E)
     hole))

(define-metafunction KafKa
  [(debug any_A) 2 (side-condition (writeln (term any_A)))])

(define (find-hole list)
  (set-first (set-subtract (list->set (stream->list (in-range 0 (+ 1 (length list))))) (list->set list))))


(define-metafunction KafKa
  alloc : σ a ... C -> (a σ)
  [(alloc ((name σa (a_1 ↦ { a_2 ... C_1})) ...) a ... C) (a_3 ((a_3 ↦ {a ... C}) σa ...)) (where a_3 ,(find-hole (term (a_1 ...))))])

(define-metafunction KafKa
  lookup-env : Γ x -> t
  [(lookup-env (x : t Γ) x) t]
  [(lookup-env (x_!_1 : t Γ) (name x x_!_1)) (lookup-env Γ x)])

(define-metafunction KafKa
  dispatch-untyped : a m a σ K -> e
  [(dispatch-untyped a_1 m a_2
                     (name σ (σa_1 ... (a_1 ↦ {a_3 ... C}) σa_2 ...))
                     (k_1 ... (class C fd ... md_1 ... (m (x anyt) anyt e) md_2 ...) k_2 ...))
   ((substitute (substitute e x a_2) this a_1) σ)])

(define Kred
  (reduction-relation KafKa
                      #:domain P
                      (--> ((in-hole E (new C a ...)) K σ)
                           ((in-hole E a_1) K σ_1)
                           (where (a_1 σ_1) (alloc σ a ... C)))
                      (--> ((in-hole E (call a_1 f))
                            (name K (k_1 ... (class C fd_1 ..._1 (f t) fd_2 ..._2 md ...) k_2 ...))
                            (name σ (σa_1 ... (a_1 ↦ {a_3 ..._1 a_4 a_5 ..._2 C}) σa_2 ...)))
                           ((in-hole E a_4) K σ))
                      (--> ((in-hole E (call a_1 f a_2)) (name K (k_1 ... (class C fd_1 ..._1 (f t) fd_2 ..._2 md ...) k_2 ...))
                                                         (name σ (σa_1 ... (a_1 ↦ {a_3 ..._1 a_4 a_5 ..._2 C}) σa_2 ...)))
                           ((in-hole E a_2) K (σa_1 ... (a_1 ↦ {a_3 ... a_2 a_5 ... C}) σa_2 ...)))
                      (--> ((in-hole E (call a f)) (name K (k_1 ... (class C fd ... md_1 ... (f t e) md_2 ...) k_2 ...))
                                                   (name σ (σa_1 ... (a_1 ↦ {a_3 ... C}) σa_2 ...)))
                           ((in-hole E (substitute e this a_1)) K σ))
                      (--> ((in-hole E (call a_1 f a_2)) (name K (k_1 ... (class C fd ... md_1 ... (f (x t_1) t e) md_2 ...) k_2 ...))
                                                         (name σ (σa_1 ... (a_1 ↦ {a_3 ... C}) σa_2 ...)))
                           ((in-hole E (substitute (substitute e x a_2) this a_1)) K σ))
                      (--> ((in-hole E (call a_1 m a_2)) (name K (k_1 ... (class C fd ... md_1 ... (m (x C_1) C_2 e) md_2 ...) k_2 ...))
                                                         (name σ (σa_1 ... (a_1 ↦ {a_3 ... C}) σa_2 ...)))
                           ((in-hole E (substitute (substitute e x a_2) this a_1)) K σ))
                      (--> ((in-hole E (dcall a_1 m a_2)) (name K (k_1 ... (class C fd ... md_1 ... (m (x anyt) anyt e) md_2 ...) k_2 ...))
                                                          (name σ (σa_1 ... (a_1 ↦ {a_3 ... C}) σa_2 ...)))
                           ((in-hole E (substitute (substitute e x a_2) this a_1)) K σ))
                      (--> ((in-hole E (subcast anyt a)) K σ) ((in-hole E a) K σ))
                      (--> ((in-hole E (subcast D a)) K (name σ (σa_1 ... (a ↦ {a_1 ... C}) σa_2 ...)))
                           ((in-hole E a) K σ)
                           (judgment-holds (<: () K C D)))
                      (--> ((in-hole E (namcast D a)) K (name σ (σa_1 ... (a ↦ {a_1 ... C}) σa_2 ...)))
                           ((in-hole E a) K σ)
                           (judgment-holds (namesub C D K)))))
  

(define-metafunction KafKa
  mtypes : C K -> (mt ...)
  [(mtypes C (k_1 ... (class C (f t) ... (m (x t_1) ... t_2 e) ...) k_2 ...)) ((f t) ... (f t t) ... (m t_1 ... t_2) ...)]
  [(mtypes C_!_1 ((class C_!_1 fd ... md ...) ...)) ()])

(define-metafunction KafKa
  compose-K : K ... -> K
  [(compose-K (k_1 ...) (k_2 ...) K ...) (compose-K (k_1 ... k_2 ...) K ...)]
  [(compose-K K) K])

(define-metafunction KafKa
  names : mt -> n
  ((names (m t_1 t_2)) m)
  ((names (f t t)) f)
  ((names (f t)) f))

(define-judgment-form KafKa
  #:mode (namesub I I I)
  #:contract (namesub C C K)
  [(where (mt_1 ...) (mtypes C_1 K))
   (where (mt_2 ...) (mtypes C_2 K))
   (where (n_1 ...) ((names mt_1) ...))
   (where (n_2 ...) ((names mt_2) ...))
   (side-condition ,(subset? (term (n_1 ...)) (term (n_2 ...))))
   ------
   (namesub C_1 C_2 K)])

(define-extended-language KafKa<: KafKa
  (M ((C <: D) ...)))

(define-judgment-form KafKa<:
  #:mode (<: I I I I)
  [-------"SRef"
   (<: M K t t)]
  [-------"SAss"
   (<: ( (C_1 <: C_2) ... (C <: D) (C_3 <: C_4) ...) K C D)]
  [(where (mt ...) (mtypes D K))
   (where M_1 ((C <: D) (C_1 <: C_2) ...))
   (where ((C_!_1 <: D_!_1) ...) M)
   (where (C_!_2 C_!_2) (C D))
   (<: M_1 K mt (mtypes C K)) ...
   --------"SRec"
   (<: (name M ((C_1 <: C_2) ...)) K (name C C_!_1) (name D D_!_1))]
  [(<: M K mt mt_2)
   ---------"SRecRecurs"
   (<: M K mt (mt_1 ... mt_2 mt_3 ...))]
  [(<: M K t_1 t_2)
   (<: M K t_4 t_3)
   ----------"SMet"
   (<: M K (m t_1 t_3) (m t_2 t_4))]
  [(<: M K t_1 t_2)
   (<: M K t_4 t_3)
   ----------"SSet"
   (<: M K (f t_1 t_3) (f t_2 t_4))]
  [(<: M K t_1 t_2)
   ----------"SGet"
   (<: M K (f t_1) (f t_2))]
  [----------"SThat"
   (<: M K (that t_1 ... t_2) mt)])

(define (make-free-class bound)
  (term ,(string->symbol (string-join (list "gen" (number->string (length bound))) ""))))

(define-metafunction KafKa
  free-class : K C ... -> C
  [(free-class ((class C fd ... md ...) ...) D ...) ,(make-free-class (term (C ... D ...)))])

;Typed Racket

(define-judgment-form KafKa
  #:mode (tr-progtrans I O)
  #:contract (tr-progtrans p p)
  [(tr-classtrans K_1 K_1 K_2) (tr-syncast K_1 · e_1 e_2 t)
   ------- "PT"
   (tr-progtrans (e_1 K_1) (e_2 K_2))])


(define-judgment-form KafKa
  #:mode (tr-classtrans I I O)
  #:contract (tr-classtrans K K K)
  [(tr-classtrans K (k_1 ...) (k_2 ...))
   (tr-methtrans K C md md_1) ...
   ------- "CR1"
   (tr-classtrans K ((class C fd ... md ...) k_1 ...) ((class C fd ... md_1 ...) k_2 ...))]
  [------
   (tr-classtrans K () ())])

(define-judgment-form KafKa
  #:mode (tr-methtrans I I I O)
  #:contract (tr-methtrans K C md md)
  [(tr-anacast K (this : C (x : t ·)) e t_1 e_1)
   ------"MT"
   (tr-methtrans K C (m (x t) t_1 e) (m (x t) t_1 e_1))])

(define-judgment-form KafKa
  #:mode (tr-syncast I I I O O)
  #:contract (tr-syncast K Γ e e t)
  [(where t (lookup-env Γ x))
   -----"TRA1"
   (tr-syncast K Γ x x t)]
  [(tr-syncast K Γ e_1 e_3 C)
   (where (mt_1 ... (n t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (tr-anacast K Γ e_2 t_1 e_4) ...
   -----"TRA2"
   (tr-syncast K Γ (call e_1 n e_2 ..._1) (call e_1 n e_4 ...) t_2)]
  [(tr-syncast K Γ e_1 e_3 anyt)
   (tr-anacast K Γ e_2 anyt e_4)
   ------"TRA3"
   (tr-syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) anyt)]
  [(where (k_1 ... (class C (f t) ..._1 md ...) k_2 ...) K)
   (tr-anacast K Γ e_1 t e_2) ...
   ------"TRA4"
   (tr-syncast K Γ (new C e_1 ..._1) (new C e_2 ...) C)])

(define-judgment-form KafKa
  #:mode (tr-anacast I I I I O)
  #:contract (tr-anacast K Γ e t e)
  [(tr-syncast K Γ e e_1 t_1)
   (<: () K t_1 t)
   -----"TRAASC1"
   (tr-anacast K Γ e t e_1)]
  [(tr-syncast K Γ e e_1 t_1)
   (side-condition ,(not (judgment-holds (<: () K t t_1))))
   -----"TRAASC2"
   (tr-anacast K Γ e t (behcast t (namcast t e)))])

(define Kred-beh
  (extend-reduction-relation
   Kred KafKa
   (--> ((in-hole E (behcast t a)) K σ)
        ((in-hole E a_1) K_1 σ_1)
        (where (K_1 a_1 σ_1) (behcast-impl a t σ K)))))

(define-metafunction KafKa
  behcast-impl : a t σ K -> (K a σ)
  ((behcast-impl a C_1 σ (name K (k ...)))
   ((k_1 k ...) a_2 σ_1)
   (where (σa_1 ... (a ↦ {a_1 ... C}) σa_2 ...) σ)
   (where D (free-class (k ...)))
   (where k_1 (wrap-t C (get-mds C K) (mtypes C K) (mtypes C_1 K) D))
   (where (a_2 σ_1) (alloc σ a D)))
  ((behcast-impl a anyt σ (name K (k ...)))
   ((k_1 k ...) a_2 σ_1)
   (where (σa_1 ... (a ↦ {a_1 ... C}) σa_2 ...) σ)
   (where D (free-class (k ...)))
   (where k_1 (wrap-ut C (get-mds C K) (mtypes C K) D))
   (where (a_2 σ_1) (alloc σ a D))))
   
               
(define-metafunction KafKa
  wrap-t : C (md ...) (mt ...) (mt ...) D -> k
  [(wrap-t C (md_1 ...) (mt_1 ...) (mt_2 ...) D)
   (class D (that C) md ...)
   (where (md ...) ,(judgment-holds (wrap-t-mths (md_1 ...) (mt_1 ...) (mt_2 ...) md) md))])

(define-metafunction KafKa
  wrap-ut : C (md ...) (mt ...) D -> k
  [(wrap-ut C (md ...) (mt ...) D)
   (class D (that C) md_1 ...)
   (where (md_1 ...) ,(judgment-holds (wrap-ut-mths (md ...) (mt ...) md_1) md_1))
   ])

(define-metafunction KafKa
  behnamcast : t e -> e
  ((behnamcast t e) (behcast t (namcast t e))))

(define-judgment-form KafKa
  #:mode (wrap-t-mths I I I O)
  #:contract (wrap-t-mths (md ...) (mt ...) (mt ...) md)
  [(side-condition ,(not (redex-match KafKa that (term f))))
   ----- "R1"
   (wrap-t-mths _
                (mt_1 ... (f t) mt_2 ...)
                (mt_3 ... (f t_1) mt_4 ...)
                (f t_1 (behnamcast t_1 (call (call this that) f))))]
  [(side-condition ,(not (redex-match KafKa that (term f))))
   ----- "R2"
   (wrap-t-mths _
                (mt_1 ... (f t t) mt_2 ...)
                (mt_3 ... (f t_1 t_1) mt_4 ...)
                (f (y t_1) t_1 (behnamcast t_1 (call (call this that) f (behcast t y)))))]
  [(beh-lift (mt ...) (mt_1 ... (m t t_1) mt_2 ...) (behcast C_1 x) x e e_1)
   ----- "R3"
   (wrap-t-mths (md_1 ... (m (x C_1) C_2 e) md_2 ...) (mt ...) (mt_1 ... (m t t_1) mt_2 ...)
                (m (x t) t_1 (behnamcast t_1 e_1)))]
  [(side-condition ,(not (redex-match KafKa (m (md_3 ... (m (x anyt) anyt) md_4 ...)) (term (m (md_1 ... md_2 ...))))))
   ---- "R4"
   (wrap-t-mths (md_1 ... (m (x C_1) C_2 e) md_2 ...) (mt ...) (mt_1 ... (m t t_1) mt_2 ...)
                (m (x anyt) anyt (subcast anyt (call this m (behnamcast t x)))))]
  [(beh-lift (mt ...) (mt_1 ... (m t t_1) mt_2 ...) (behcast anyt x) x e e_1)
   ---- "R5"
   (wrap-t-mths (md_1 ... (m (x anyt) anyt e) md_2 ...) (mt ...) (mt_1 ... (m t t_1) mt_2 ...)
                (m (x t) t_1 (behnamcast t_1 e_1)))]
  [(side-condition ,(not (redex-match KafKa ((f t) (mt_1 ... (f t) mt_2 ...)) (term ((f t) (mt_3 ...))))))
   (side-condition ,(not (redex-match KafKa that (term f))))
   --- "R6"
   (wrap-t-mths (md ...) (mt_1 ... (f t) mt_2 ..) (mt_3 ...)
                (f t (call (call this that) f)))]
  [(side-condition ,(not (redex-match KafKa ((f t t) (mt_1 ... (f t) mt_2 ...)) (term ((f t t) (mt_3 ...))))))
   (side-condition ,(not (redex-match KafKa that (term f))))
   --- "R7"
   (wrap-t-mths (md ...) (mt_1 ... (f t t) mt_2 ..) (mt_3 ...)
                (f (y t) t (call (call this that) f y)))]
  [(side-condition ,(not (redex-match KafKa (m (mt_1 ... (m t_1 t_2) mt_2 ...)) (term (m (mt_1 ...))))))
   (beh-lift (mt ...) (mt_1 ...) x x e e_1)
   ---- "R8"
   (wrap-t-mths (md_1 ... (m (x C_1) C_2 e) md_2 ...) (mt ...) (mt_1 ...)
                (m (x C_1) C_2 e_1))]
  [(side-condition ,(not (redex-match KafKa (m (mt_1 ... (m t_1 t_2) mt_2 ...)) (term (m (mt_1 ...))))))
   (beh-lift (mt ...) (mt_1 ...) x x e e_1)
   ---- "R9"
   (wrap-t-mths (md_1 ... (m (x anyt) anyt e) md_2 ...) (mt ...) (mt_1 ...)
                (m (x anyt) anyt e_1))])

(define-judgment-form KafKa
  #:mode (wrap-ut-mths I I O)
  #:contract (wrap-ut-mths (md ...) (mt ...) md)
  [(side-condition ,(not (redex-match KafKa that (term f))))
   ---- "R1"
   (wrap-ut-mths (md ...)
                 (mt_1 ... (f t) mt_2 ...)
                 (f anyt (behcast anyt (call (call this that) f))))]
  [(side-condition ,(not (redex-match KafKa that (term f))))
   ---- "R2"
   (wrap-ut-mths (md ...)
                 (mt_1 ... (f t t) mt_2 ...)
                 (f (y anyt) anyt (behcast anyt (call (call this that) f (behcast t y)))))]
  [(beh-lift (mt ...) ((dynamize mt) ...) (behnamcast t x) x e e_1)
   ---- "R3"
   (wrap-ut-mths (md_1 ... (m (x t) t_1 e) md_2 ...) (mt ...)
                 (m (x anyt) anyt (behcast anyt e_1)))])

(define-metafunction KafKa
  dynamize : mt -> mt
  ((dynamize (f t)) (f anyt))
  ((dynamize (f t t)) (f anyt anyt))
  ((dynamize (m t_1 t_2)) (m anyt anyt)))
                 

(define-metafunction KafKa
  get-mds : C K -> (md ...)
  [(get-mds C (k_1 ... (class C fd ... md ...) k_2 ...)) (md ...)])
  

(define-judgment-form KafKa
  #:mode (beh-lift I I I I I O)
  #:contract (beh-lift (mt ...) (mt ...) e x e e)
  [-------------- "REW1"
   (beh-lift (mt_1 ...) (mt_2 ...) e_1 x x e_1)]
  [-------------- "REW2"
   (beh-lift (mt_1 ...) (mt_2 ...) e_1 (name x x_!_1) (name x_1 x_!_1) x_1)]
  [(beh-lift mt_i mt_t e_1 x e e_2) ...
   (side-condition ,(or
                      (redex-match KafKa f (term n))
                      (not (redex-match KafKa anyt (term t_2)))))
   -------------- "REW3"
   (beh-lift (name mt_i (mt_1 ... (n t_1 ..._1 t_2) mt_3 ...))
             (name mt_t (mt_2 ... (n t_3 ..._1 t_4) mt_4 ...)) e_1 x
             (call this n e ..._1) (call this n (behcast t_3 e_2) ...))]
  [(beh-lift mt_i mt_t e_1 x e e_2)
   -------------- "REW4"
   (beh-lift (name mt_i (mt_1 ... (m t_1 t_2) mt_3 ...))
             (name mt_t (mt_2 ... (m anyt anyt) mt_4 ...)) e_1 x
             (call this m e) (dcall this m (behcast anyt e_2)))]
  [(beh-lift mt_i mt_t e_1 x e e_2) ...
   (side-condition ,(not (redex-match KafKa ((n t_1 ..._1)
                                             (mt_1 ... (n t_2 ..._1 t_3) mt_2 ...))
                                      (term ((n t_1 ...) (mt_2 ...))))))
   -------------- "REW5"
   (beh-lift (name mt_i (mt_1 ... (n t_1 ..._1 t_2) mt_3 ...))
             (name mt_t (mt_2 ...)) e_1 x
             (call this n e ..._1) (call this n e_2 ...))]
  [(beh-lift mt_i mt_t e_a x e e_2)
   (beh-lift mt_i mt_t e_a x e_1 e_3) ...
   (side-condition ,(not (redex-match KafKa this (term e))))
   -------------- "REW6"
   (beh-lift (name mt_i (mt_1 ...))
             (name mt_t (mt_2 ...)) e_a x
             (call e n e_1 ..._1) (call e_2 n e_3 ...))]
  [(beh-lift mt_i mt_t e_a x e e_2)
   (beh-lift mt_i mt_t e_a x e_1 e_3)
   -------------- "REW7"
   (beh-lift (name mt_i (mt_1 ...))
             (name mt_t (mt_2 ...)) e_a x
             (dcall e m e_1) (dcall e_2 m e_3))]
  [(beh-lift (mt_1 ...) (mt_2 ...) e_a x e e_1) ...
   -------------- "REW8"
   (beh-lift (mt_1 ...) (mt_2 ...) e_a x
             (new C e ...) (new C e_1 ...))]
  [(beh-lift (mt_1 ...) (mt_2 ...) e_a x e e_1)
   -------------- "REW9"
   (beh-lift (mt_1 ...) (mt_2 ...) e_a x
             (behcast t e) (behcast t e_1))]
  [(beh-lift (mt_1 ...) (mt_2 ...) e_a x e e_1)
   -------------- "REW10"
   (beh-lift (mt_1 ...) (mt_2 ...) e_a x
             (namcast t e) (namcast t e_1))]
  [(beh-lift (mt_1 ...) (mt_2 ...) e_a x e e_1)
   -------------- "REW11"
   (beh-lift (mt_1 ...) (mt_2 ...) e_a x
             (subcast t e) (subcast t e_1))])
; Thorn


(define-extended-language Thorn KafKa
  (t .... (weak C)))


(define-judgment-form Thorn
  #:mode (thorn-progtrans I O)
  #:contract (thorn-progtrans p p)
  [(thorn-classtrans K_1 K_1 K_2) (thorn-syncast K_1 · e_1 e_2 t)
   ------- "PT"
   (thorn-progtrans (e_1 K_1) (e_2 K_2))])


(define-judgment-form Thorn
  #:mode (thorn-classtrans I I O)
  #:contract (thorn-classtrans K K K)
  [(thorn-classtrans K (k_1 ...) (k_2 ...))
   (thorn-methtrans K C md md_1) ...
   ------- "CR1"
   (thorn-classtrans K ((class C fd ... md ...) k_1 ...) ((class C fd ... md_1 ...) k_2 ...))]
  [------
   (thorn-classtrans K () ())])

(define-judgment-form Thorn
  #:mode (thorn-methtrans I I I O)
  #:contract (thorn-methtrans K C md md)
  [(thorn-anacast K (this : C (x : t ·)) e t_1 e_1)
   ------"MT"
   (thorn-methtrans K C (m (x t) t_1 e) (m (x t) t_1 e_1))])

(define-extended-language Thorn<: Thorn
  (M ((C <: D) ...)))

(define-judgment-form Thorn<:
  #:mode (<:t I I I I)
  [-------"THSRef"
   (<:t M K t t)]
  [(<:t M K C D)
   -------"THSWeak"
   (<:t M K (weak C) (weak D))]
  [(<:t M K C D)
   -------"THSLower"
   (<:t M K C (weak D))]
  [-------"THSAss"
   (<:t ( (C_1 <: C_2) ... (C <: D) (C_3 <: C_4) ...) K C D)]
  [(where (mt ...) (mtypes-thorn D K))
   (where M_1 ((C <: D) (C_1 <: C_2) ...))
   (where ((C_!_1 <: D_!_1) ...) M)
   (where (C_!_2 C_!_2) (C D))
   (<:t M_1 K mt (mtypes-thorn C K)) ...
   --------"THSRec"
   (<:t (name M ((C_1 <: C_2) ...)) K (name C C_!_1) (name D D_!_1))]
  [(<:t M K mt mt_2)
   ---------"THSRecRecurs"
   (<:t M K mt (mt_1 ... mt_2 mt_3 ...))]
  [(<:t M K t_1 t_2)
   (<:t M K t_4 t_3)
   ----------"THSMet"
   (<:t M K (m t_1 t_3) (m t_2 t_4))]
  [(<:t M K t_1 t_2)
   ----------"THSGet"
   (<:t M K (f t_1) (f t_2))]
  [----------"THSThat"
   (<:t M K (that t_1 ... t_2) mt)])


(define-judgment-form Thorn
  #:mode (thorn-syncast I I I O O)
  #:contract (thorn-syncast K Γ e e t)
  [(where t (lookup-env Γ x))
   -----"THA1"
   (thorn-syncast K Γ x x t)]
  [(thorn-syncast K Γ e_1 e_3 C)
   (where (mt_1 ... (n t_1 ..._1 t_2) mt_2 ...) (mtypes-thorn C K))
   (thorn-anacast K Γ e_2 t_1 e_4) ...
   -----"THA2"
   (thorn-syncast K Γ (call e_1 n e_2 ..._1) (call e_1 n e_4 ...) t_2)]
  
  [(thorn-syncast K Γ e_1 e_3 (weak C))
   (where (mt_1 ... (m t_1 D) mt_2 ...) (mtypes-thorn C K))
   (thorn-anacast K Γ e_2 t_1 e_4)
   -----"THA3"
   (thorn-syncast K Γ (call e_1 m e_2) (subcast D (dcall e_3 m e_4)) D)]
  
  [(thorn-syncast K Γ e_1 e_3 (weak C))
   (where (mt_1 ... (m t_1 t_2) mt_2 ...) (mtypes-thorn C K))
   (side-condition ,(not (redex-match Thorn D (term t_2))))
   (thorn-anacast K Γ e_2 t_1 e_4)
   -----"THA4"
   (thorn-syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) t_2)]
  
  [(thorn-syncast K Γ e_1 e_3 anyt)
   (thorn-anacast K Γ e_2 anyt e_4)
   ------"THA5"
   (thorn-syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) anyt)]
  
  [(where (k_1 ... (class C (f t) ..._1 md ...) k_2 ...) K)
   (thorn-anacast K Γ e_1 t e_2) ...
   ------"THA6"
   (thorn-syncast K Γ (new C e_1 ..._1) (new C e_2 ...) C)])

(define-judgment-form Thorn
  #:mode (thorn-anacast I I I I O)
  #:contract (thorn-anacast K Γ e t e)
  [(thorn-syncast K Γ e_1 e_2 C_2)
   (<:t () K C_2 C_1)
   -----"THAASC1"
   (thorn-anacast K Γ e_1 C_1 e_2)]
  
  [(thorn-syncast K Γ e_1 e_2 (weak D))
   (<:t () K D C)
   -----"THAASC2"
   (thorn-anacast K Γ e_1 C (subcast C e_2))]
  
  [(thorn-syncast K Γ e_1 e_2 anyt)
   -----"THAASC3"
   (thorn-anacast K Γ e_1 C (subcast C e_2))]
  
  [(thorn-syncast K Γ e_1 e_2 anyt)
   -----"THAASC4"
   (thorn-anacast K Γ e_1 (weak C) e_2)]

  [(thorn-syncast K Γ e_1 e_2 t)
   (side-condition ,(not (redex-match Thorn anyt (term t))))
   -----"THAASC5"
   (thorn-anacast K Γ e_1 anyt e_2)])


(define-metafunction/extension mtypes Thorn
  mtypes-thorn : C K -> (mt ...))

; Reticulated

(define-extended-language KMeet KafKa
  (Pb (C C ↦ C))
  (P (Pb ...)))

(define-judgment-form KMeet
  #:mode (in-P I I I O)
  #:contract (in-P C C P C)
  [------"IP1"
   (in-P C D (Pb_1 ... (C D ↦ C_1) Pb_2 ...) C_1)]
  [------"IP2"
   (in-P C D (Pb_1 ... (D C ↦ C_1) Pb_2 ...) C_1)])

(define-judgment-form KMeet
  #:mode (tmeet I I I I O O)
  #:contract (tmeet t t P K t K)
  [-----"TM1"
   (tmeet C anyt P K C K)]
  [-----"TM2"
   (tmeet anyt C P K C K)]
  [-----"TM3"
   (tmeet t t P K t K)]
  [(where C_E (free-class K C_3 ...))
   (where P_1 ((C D ↦ C_E) (C_1 C_2 ↦ C_3) ...))
   (side-condition ,(not (judgment-holds (in-P C D P C_4))))
   (where (mt ...) (mtypes C K))
   (where (mt_1 ...) (mtypes D K))
   (mmeet (mt ...) (mt_1 ...) P_1 K (mt_2 ...) (k ...))
   (where K_2 ((typegen (mt_2 ...) C_E) k ...))
   -----"TM4"
   (tmeet (name C C_!_1) (name D D_!_1) (name P ((C_1 C_2 ↦ C_3) ...)) K C_E K_2)]
  [(in-P C D P C_1)
   -----"TM5"
   (tmeet C D P K C_1 K)])

(define-judgment-form KMeet
  #:mode (mmeet I I I I O O)
  #:contract (mmeet mts mts P K mts K)
  [----"MM1"
   (mmeet mts () P K mts K)]
  [----"MM2"
   (mmeet () mts P K mts K)]
  [(tmeet t t_1 P K t_2 K_1)
   ----"MM3"
   (mmeet ((f t)) (mt_1 ... (f t_1) mt_2 ...) P K ((f t_2)) K_1)]
  [(tmeet t t_1 P K t_2 K_1)
   ----"MM4"
   (mmeet ((f t t)) (mt_1 ... (f t_1 t_1) mt_2 ...) P K ((f t_2 t_2)) K_1)]
  [(tmeet t_3 t_1 P K t_5 K_1)
   (tmeet t_2 t_4 P K_1 t_6 K_2)
   ----"MM5"
   (mmeet ((m t_1 t_2)) (mt_1 ... (m t_3 t_4) mt_2 ...) P K ((m t_5 t_6)) K_1)]
  [(mmeet (mt) (mt_4 ...) P K (mt_5) K_1)
   (mmeet (mt_2 mt_3 ...) (mt_4 ...) P K_1 (mt_6 ...) K_2)
   ----"MM6"
   (mmeet (mt mt_2 mt_3 ...) (mt_4 ...) P K (mt_5 mt_6 ...) K_1)])

(define-metafunction KafKa
  typegen : mts C -> k
  [(typegen ((m t_1 t_2) mt ...) C) (class C (m (x t_1) t_2 (subcast t_2 x)) md ...) (where (class C md ...) (typegen (mt ...) C))]
  [(typegen ((f t t) mt ...) C) (class C (f (x t) t x) md ...) (where (class C md ...) (typegen (mt ...) C))]
  [(typegen ((f t) mt ...) C) (class C (f t (subcast t (new C))) md ...) (where (class C md ...) (typegen (mt ...) C))]
  [(typegen () C) (class C)])

(define-judgment-form KafKa
  #:mode (consistent I I I)
  #:contract (consistent K t t)
  [(tmeet t_1 t_2 () K t K_1)
   ----"C1"
   (consistent K t_1 t_2)])

 ; transient

(define-judgment-form KafKa
  #:mode (trans-progtrans I O)
  #:contract (trans-progtrans p p)
  [(trans-classtrans K_1 K_1 (k ...)) (tr-syncast K_1 · e_1 e_2 t)
   ------- "PT"
   (trans-progtrans (e_1 K_1) (e_2 ((class A2 (f1 anyt) (f2 anyt)) k ...)))])


(define-judgment-form KafKa
  #:mode (trans-classtrans I I O)
  #:contract (trans-classtrans K K K)
  [(trans-classtrans K (k_1 ...) (k_2 ...))
   (trans-methtrans K C md md_1) ...
   ------- "CR1"
   (trans-classtrans K ((class C fd ... md ...) k_1 ...) ((class C fd ... md_1 ...) k_2 ...))]
  [------
   (trans-classtrans K () ())])

(define-judgment-form KafKa
  #:mode (trans-methtrans I I I O)
  #:contract (trans-methtrans K C md md)
  [(trans-anacast K (this : C (x : anyt ·)) e anyt e_1)
   ------"MTU"
   (trans-methtrans K C (m (x anyt) anyt e) (m (x anyt) anyt e_1))]
  [(trans-anacast K (this : C (x : C_1 ·)) e anyt e_1)
   ------"MTT"
   (trans-methtrans K C (m (x C_1) C_2 e)
                    (m (x anyt) anyt (subcast anyt (call (new A2 (namcast C_1 x) e_1) f2))))])

(define-judgment-form KafKa
  #:mode (trans-syncast I I I O O)
  #:contract (trans-syncast K Γ e e t)
  [(where t (lookup-env Γ x))
   -----"GRA1"
   (trans-syncast K Γ x (namcast t x) t)]
  [(trans-syncast K Γ e_1 e_3 C)
   (where (mt_1 ... (m t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (side-condition ,(not (redex-match KafKa this (term e_1))))
   (trans-anacast K Γ e_2 t_1 e_4) ...
   -----"GRA2"
   (trans-syncast K Γ (call e_1 m e_2 ..._1) (namcast t_2 (dcall (subcast anyt e_1) m (subcast anyt e_4) ...)) t_2)]
  [(trans-syncast K Γ e_1 e_3 anyt)
   (trans-anacast K Γ e_2 anyt e_4)
   ------"GRA3"
   (trans-syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) anyt)]
  [(where C (lookup-env Γ this))
   (where (mt_1 ... (f t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (trans-anacast K Γ e t_1 e_1) ...
   ------"GRA4"
   (trans-syncast K Γ (call this f e ..._1) (call this f e_1 ...) anyt)]
  [(where (k_1 ... (class C (f t) ..._1 md ...) k_2 ...) K)
   (trans-anacast K Γ e_1 t e_2) ...
   ------"GRA5"
   (trans-syncast K Γ (new C e_1 ..._1) (new C e_2 ...) C)])

(define-judgment-form KafKa
  #:mode (trans-anacast I I I I O)
  #:contract (trans-anacast K Γ e t e)
  [(trans-syncast K Γ e e_1 t_1)
   (<: () K t t_1)
   -----"GRAASC1"
   (trans-anacast K Γ e t e_1)]
  [(trans-syncast K Γ e e_1 t_1)
   (consistent K t t_1)
   -----"GRAASC2"
   (trans-anacast K Γ e t e_1)])

; monotonic


(define-judgment-form KafKa
  #:mode (mono-progtrans I O)
  #:contract (mono-progtrans p p)
  [(mono-classtrans K_1 K_1 (k ...)) (tr-syncast K_1 · e_1 e_2 t)
   ------- "PT"
   (mono-progtrans (e_1 K_1) (e_2 ((class A2 (f1 anyt) (f2 anyt)) k ...)))])

(define-judgment-form KafKa
  #:mode (mono-class-wrap I I O O)
  #:contract (mono-class-wrap t K t K)
  [(where D (free-class K))
   (where k (monWrap C (mtypes C K) (mtypes C K) D K))
   ------- "MW1"
   (mono-class-wrap C K D (k))]
  [------ "MW2"
   (mono-class-wrap anyt K anyt ())])

(define-judgment-form KafKa
  #:mode (mono-classtrans I I O)
  #:contract (mono-classtrans K K K)
  [(mono-classtrans K (k_1 ...) (k_2 ...))
   (mono-methtrans K C md md_1 (k_m ...)) ...
   (mono-class-wrap t (k_2 ...) t_1 (k_3 ...)) ...
   ------- "CR1"
   (mono-classtrans K ((class C (f t) ... md ...) k_1 ...) ((class C (f t_1) ... md_1 ...) k_2 ... k_m ... ... k_3 ... ...))]
  [------
   (mono-classtrans K () ())])

(define-judgment-form KafKa
  #:mode (mono-methtrans I I I O O)
  #:contract (mono-methtrans K C md md K)
  [(mono-anacast K (this : C (x : t_1 ·)) e t_2 e_1)
   (mono-class-wrap t_1 K t_3 (k_1 ...))
   (mono-class-wrap t_2 K t_4 (k_2 ...))
   ------"MT"
   (mono-methtrans K C (m (x t_1) t_2 e) (m (x t_3) t_4 e_1) (k_1 ... k_2 ...))])

(define-judgment-form KafKa
  #:mode (mono-syncast I I I O O)
  #:contract (mono-syncast K Γ e e t)
  [(where t (lookup-env Γ x))
   -----"MOA1"
   (mono-syncast K Γ x x t)]
  [(mono-syncast K Γ e_1 e_3 C)
   (where (mt_1 ... (m t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (side-condition ,(not (redex-match KafKa this (term e_1))))
   (mono-anacast K Γ e_2 t_1 e_4) ...
   -----"MOA2"
   (mono-syncast K Γ (call e_1 n e_2 ..._1) (call e_3 n e_4 ...) t_2)]
  [(mono-syncast K Γ e_1 e_3 anyt)
   (mono-anacast K Γ e_2 anyt e_4)
   ------"MOA3"
   (mono-syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) anyt)]
  [(where C (lookup-env Γ this))
   (where (mt_1 ... (f t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (mono-anacast K Γ e t_1 e_1) ...
   ------"MOA4"
   (mono-syncast K Γ (call this f e ..._1) (call this f e_1 ...) anyt)]
  [(where (k_1 ... (class C (f t) ..._1 md ...) k_2 ...) K)
   (mono-anacast K Γ e_1 t e_2) ...
   ------"MOA5"
   (mono-syncast K Γ (new C e_1 ..._1) (new C e_2 ...) C)])

(define-judgment-form KafKa
  #:mode (mono-anacast I I I I O)
  #:contract (mono-anacast K Γ e t e)
  [(mono-syncast K Γ e e_1 t_1)
   (<: () K t t_1)
   -----"MOAASC1"
   (mono-anacast K Γ e t e_1)]
  [(mono-syncast K Γ e e_1 t_1)
   (consistent K t t_1)
   -----"MOAASC2"
   (mono-anacast K Γ e t e_1)])


;litmus

(define litmusAux (term ((class C (mn (x C) C this)) (class D (mo (x D) D this)))))
(define litmusProg (term (call (new T) mt (new A))))

(define litmusK1 (term ((class A (mm (x A) A this))
                        (class I (mn (x I) I this))
                        (class T (mt (x I) T this)))))
(define litmusK1f (term (compose-K ,litmusAux ,litmusK1)))

(define litmusK2 (term ((class A (mm (x A) A this))
                        (class I (mm (x C) I this))
                        (class T (mt (x I) T this)))))
(define litmusK2f (term (compose-K ,litmusAux ,litmusK2)))

(define litmusK3 (term ((class A (mm (x anyt) anyt this))
                        (class I (mm (x C) C this))
                        (class I2 (mm (x D) D this))
                        (class E (ff I) (fg I2))
                        (class T (mt (x A) E (new E x x))))))

(define litmusK3f (term (compose-K ,litmusAux ,litmusK3)))

(define litmusK4 (term ((class A
                          (ff anyt)
                          (mm (x A) A
                             (call this ff (new A (new C)))))
                        (class I
                          (ff D)
                          (mm (x I) I this))
                        (class T
                          (mt (x I) I (call x mm x))))))
(define litmusK4f (term (compose-K ,litmusAux ,litmusK4)))

(define litmus1 (term (,litmusProg ,litmusK1f)))
(define litmus2 (term (,litmusProg ,litmusK2f)))
(define litmus3 (term (,litmusProg ,litmusK3f)))

(define litmusProg4 (term (call (new T) mt (new A (new D)))))
(define litmus4 (term (,litmusProg4 ,litmusK4f)))

;other examples from the paper

(define meetex1 (term ((class A (mm (x anyt) A this)) (class B (mm (x B) anyt this)))))
(define meetex2 (term ((class A (mm (x A) anyt this)) (class B (mm (x B) anyt this)))))

;tests for redex

(define fieldprog (term ((class A (f (x anyt) anyt x) (f anyt (new A))))))

(test--> Kred (term ((new A) ,litmusK1f ())) (term (0 ,litmusK1f ((0 ↦ {A})))))
(test--> Kred (term ((call 0 mm 0) ,litmusK1f ((0 ↦ {A})))) (term (0 ,litmusK1f ((0 ↦ {A})))))
(test--> Kred (term ((call 0 ff) ,litmusK4f ((0 ↦ {1 A})))) (term (1 ,litmusK4f ((0 ↦ {1 A})))))
(test--> Kred (term ((call 0 ff 2) ,litmusK4f ((0 ↦ {1 A})))) (term (2 ,litmusK4f ((0 ↦ {2 A})))))
(test--> Kred (term ((call 0 f) ,fieldprog ((0 ↦ {A})))) (term ((new A) ,fieldprog ((0 ↦ {A})))))
(test--> Kred (term ((call 0 f 1) ,fieldprog ((0 ↦ {A})))) (term (1 ,fieldprog ((0 ↦ {A})))))