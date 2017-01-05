#lang racket
(require racket/set)
(require redex)
(require redex/reduction-semantics)

(define-language KafKa
  (e x
     v
     (call e m e)
     (call e f)
     (dcall e m e)
     (new C e ...)
     (subcast t e)
     (namcast t e)
     (behcast t e)
     (moncast t e))
  (k (class C fd ... md ...))
  (mt (m t t) (m t))
  (t anyt C)
  (fd (f t))
  (md (m (x t) t e) (f t e))
  (C D f m n x ::= (variable-except :))
  (Γ · (x : t Γ))
  (K (k ...))
  (p (e K))
  (a number)
  (v a)
  (P E)
  (σ · (number ↦ {number ... C} σ))
  (E (call E m e)
     (call E f)
     (call v m E)
     (dcall E m e)
     (dcall v m E)
     (new C v ... E e ...)
     (subcast t E)
     (namcast t E)
     (behcast t E)
     (moncast t E)
     hole))


(define-metafunction KafKa
  lookup-env : Γ x -> t
  [(lookup-env (x : t Γ) x) t]
  [(lookup-env (x_!_1 : t Γ) (name x x_!_1)) (lookup-env Γ x)])

(define-judgment-form KafKa
  #:mode (progtrans I O)
  #:contract (progtrans p p)
  [(classtrans K_1 K_1 K_2) (syncast K_1 · e_1 e_2 t)
   ------- "PT"
   (progtrans (e_1 K_1) (e_2 K_2))])


(define-judgment-form KafKa
  #:mode (classtrans I I O)
  #:contract (classtrans K K K)
  [(classtrans K (k_1 ...) (k_2 ...))
   (methtrans K C md md_1) ...
   ------- "CR1"
   (classtrans K ((class C fd ... md ...) k_1 ...) ((class C fd ... md_1 ...) k_2 ...))]
  [------
   (classtrans K () ())])

(define-judgment-form KafKa
  #:mode (methtrans I I I O)
  #:contract (methtrans K C md md)
  [(anacast K (this : C (x : t ·)) e t_1 e_1)
   ------"MT"
   (methtrans K C (m (x t) t_1 e) (m (x t) t_1 e_1))])

(define-judgment-form KafKa
  #:mode (syncast I I I O O)
  #:contract (syncast K Γ e e t)
  [(where t (lookup-env Γ x))
   -----"A1"
   (syncast K Γ x x t)]
  [(syncast K Γ e_1 e_3 C)
   (where (mt_1 ... (m t_1 ..._1 t_2) mt_2 ...) (mtypes C K))
   (anacast K Γ e_2 t_1 e_4) ...
   -----"A2"
   (syncast K Γ (call e_1 m e_2 ..._1) (call e_1 m e_4 ...) t_2)]
  [(syncast K Γ e_1 e_3 anyt)
   (anacast K Γ e_2 anyt e_4)
   ------"A8"
   (syncast K Γ (call e_1 m e_2) (dcall e_3 m e_4) anyt)]
  [(where (k_1 ... (class C (f : t) ..._1 md ...) k_2 ...) K)
   (anacast K Γ e_1 t e_2) ...
   ------"A11"
   (syncast K Γ (new C e_1 ..._1) (new C e_2 ...) C)])

(define-judgment-form KafKa
  #:mode (anacast I I I I O)
  #:contract (anacast K Γ e t e)
  [(syncast K Γ e e_1 t_1)
   (<: () K t t_1)
   -----"AASC1"
   (anacast K Γ e t e_1)]
  [(syncast K Γ e e_1 t_1)
   (side-condition ,(not (judgment-holds (<: () K t_1 t))))
   -----"AASC2"
   (anacast K Γ e t (behcast t (namcast t e)))])

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
   ----------"SGet"
   (<: M K (f t_1) (f t_2))]
  [----------"SThat"
   (<: M K (that t_1 ... t_2) mt)])

(define-metafunction KafKa
  mtypes : C K -> (mt ...)
  [(mtypes C (k_1 ... (class C (f t) ... (m (x t_1) ... t_2 e) ...) k_2 ...)) ((f t) ... (f t t) ... (m t_1 ... t_2) ...)]
  [(mtypes C_!_1 ((class C_!_1 fd ... md ...) ...)) ()])

(define-metafunction KafKa
  compose-K : K ... -> K
  [(compose-K (k_1 ...) (k_2 ...) K ...) (compose-K (k_1 ... k_2 ...) K ...)]
  [(compose-K K) K])

(define litmusAux (term ((class C (n (x C) C this)) (class D (o (x D) D this)))))
(define litmusProg (term (call (new T) t (new A))))

(define litmusK1 (term ((class A (m (x A) A this))
                        (class I (n (x I) I this))
                        (class T (t (x I) T this)))))
(define litmusK1f (term (compose-K ,litmusAux ,litmusK1)))

(define litmusK2 (term ((class A (m (x A) A this))
                        (class I (n (x C) I this))
                        (class T (t (x I) T this)))))
(define litmusK2f (term (compose-K ,litmusAux ,litmusK2)))

(define litmusK3 (term ((class A
                          (f anyt)
                          (m (x A) A
                             (call this f (new A (new C)))))
                        (class I
                          (f D)
                          (m (x I) I this))
                        (class T
                          (t (x I) I (call x m x))))))
(define litmusK3f (term (compose-K ,litmusAux ,litmusK3)))

(define litmus1 (term (,litmusProg ,litmusK1f)))
(define litmus2 (term (,litmusProg ,litmusK2f)))
(define litmus3 (term (,litmusProg ,litmusK3f)))