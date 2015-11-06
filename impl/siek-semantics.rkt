#lang racket
(require redex)


(define-language L
  (clss (class label label ... (label t) ... (label (label t) t e ...) ...))
  (p (program clss ...))
  (e
   (call e label e ...)
   string
   integer
   (if e e e)
   (oplus e e)
   (new label (e ...) )
   (lookup e label)
   (assign e label e)
   (var label))
  (label string)
  (t
   (tdyn)
   label
   (tstr)
   (tint)
   (! label))
)

(define-extended-language L+Γ L
  [Γ · (label : t Γ) (label <: label Γ) (label (label t) ... (label (label t) t e ...) ... Γ)])

(define-judgment-form L+Γ
  #:mode (<: I I I)
  #:contract(<: Γ t t)
  [-----------
   (<: Γ t_1 t_1)]

  [----------
   (<: Γ t tdyn)]

  [(<: Γ t_1 t_2)
   -------------
   (<: (x : t Γ) t_1 t_2)]

  [(<: Γ t_1 t_2)
   ----------
   (<: (label_1 (label_2 t_3) ... Γ) t_1 t_2)]

  [------------
   (<: (label_1 <: label_2 Γ) label_1 label_2)]
  )

(define-judgment-form L+Γ
  #:mode (lookup-method I I I O O)
  #:contract (lookup-method Γ label label t t)
  [(lookup-method Γ label_1 label_2 t_1 t_2)
   ----------------
   (lookup-method (x : t Γ) label_1 label_2 t_1 t_2)]
  
  [(lookup-method Γ label_3 label_4 t_1 t_2)
   ----------------
   (lookup-method (label_1 <: label_2 Γ) label_3 label_4 t_1 t_2)]
  
  [----------------
   (lookup-method (label_1 (label_3 _) ...
                           (label_!_2 (label_4 t_4) t_3 e_1 ...) ... (label_2 (label_5 t_1) t_2 e_2 ...) (label_!_2 (label_6 t_5) t_3 e_3 ...) ... Γ) label_1 label_2 t_1 t_2)]

  [(lookup-method Γ label_1 label_2 t_1 t_2)
   --------------
   (lookup-method (label_!_1 (label_3 _) ... Γ) label_1 label_2 t_1 t_2)]
  )

(define-judgment-form L+Γ
  #:mode (lookup-field I I I O)
  #:contract (lookup-field Γ label label t)
  [(lookup-field Γ label_1 label_2 t_1)
   ----------------
   (lookup-field (x : t Γ) label_1 label_2 t_1)]
  
  [(lookup-field Γ label_3 label_4 t_1)
   ----------------
   (lookup-field (label_1 <: label_2 Γ) label_3 label_4 t_1)]
  
  [----------------
   (lookup-field (label_1 (label_!_2 _) ... (label_2 t_1) (label_!_2 _) ... Γ) label_1 label_2 t_1)]

  [(lookup-field Γ label_1 label_2 t_1)
   --------------
   (lookup-field (label_!_1 (label_!_2 _) ... Γ) label_1 label_2 t_1)]
  )

(define-judgment-form L+Γ
  #:mode (lookup-constructor I I I O)
  #:contract (lookup-constructor Γ label (t_2 ...) t)
  [(lookup-constructor Γ label_1 (t_2 ...) t_1)
   ----------------
   (lookup-constructor (x : t Γ) label_1 (t_2 ...) t_1)]
  
  [(lookup-constructor Γ label_3 (t_2 ...) t_1)
   ----------------
   (lookup-constructor (label_1 <: label_2 Γ) label_3 (t_2 ...) t_1)]
  
  [----------------
   (lookup-constructor
    (label_1 (label_3 t_2) ...
             (label_4 (label_5 t_3) ... t_4 e_1 ...) ... Γ)
    label_1 (t_2 ...) label_1)]

  [(lookup-constructor Γ label_1 (t_2 ...) t_1)
   --------------
   (lookup-constructor (label_!_1 (label_!_2 _) ... Γ) label_1 (t_2 ...) t_1)]
  )

(define-judgment-form L+Γ
  #:mode (lookup-var I I O)
  #:contract (lookup-var Γ label t)
  [(lookup-var Γ label_1 t_1)
   ----------------
   (lookup-var (label_!_1 : t Γ) label_1 t_1)]
  [
   ----------------
   (lookup-var (label_1 : t Γ) label_1 t)]
  
  [(lookup-var Γ label_3 t_1)
   ----------------
   (lookup-var (label_1 <: label_2 Γ) label_3 t_1)]
  
  [(lookup-var Γ label_1 t_1)
   ----------------
   (lookup-var
    (label_1 (label_3 t_2) ...
             (label_4 (label_5 t_3) ... t_4 e_1 ...) ... Γ)
    label_1 t_1)]
  )

(define-judgment-form L+Γ
  #:mode (types I I O)
  #:contract(types Γ e t)
  [-------------
   (types Γ integer (tint))]
  
  [-------------
   (types Γ string (tstr))]

  [(types Γ e_1 label_2)
   (lookup-method Γ label_2 label_1 t_1 t_2)
   (types Γ e_2 t_3) ...
   (<: Γ t_3 t_1) ...
   ---------------
   (types Γ (call e_1 label_1 e_2 ...) t_2)]
  
  [(types Γ e_1 (tint))
   (types Γ e_2 t_2)
   (types Γ e_3 t_2)
   --------------
   (types Γ (if e_1 e_2 e_3) t_2)]

  [(types Γ e_1 (tint))
   (types Γ e_2 (tint))
   ---------------
   (types Γ (oplus e_1 e_2) (tint))]

  [(types Γ e_1 t_2) ...
   (lookup-constructor Γ label_1 (t_2 ...) t_1)
   -------------
   (types Γ (new label_1 (e_1 ...)) t_1)
   ]
  [(types Γ e_1 label_2)
   (lookup-field Γ label_2 label_1 t_1)
   ----------
   (types Γ (lookup e_1 label_1) t_1)]
  [(types Γ e_1 label_2)
   (lookup-field Γ label_2 label_1 t_1)
   (types Γ e_2 t_2)
   (<: Γ t_2 t_1)
   -----------
   (types Γ (assign e_1 label_1 e_2) t_1)]

  [(lookup-var Γ label_1 t_1)
   -------
   (types Γ (var label_1) t_1)]
  )


