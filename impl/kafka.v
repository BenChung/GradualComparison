Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Definition id := nat.
Definition this:id := 0.
Definition ref := nat.
Inductive Cell :=
| HCell : nat * list nat -> Cell.
Definition heap := list (id * Cell).

Inductive type :=
| class : id -> type
| Any : type.
Definition env := list (id * type).

Inductive expr :=
| Var : id -> expr
| Ref : ref -> expr
| GetF : expr -> id -> expr
| SetF : expr -> id -> expr -> expr
| Call : expr -> id -> type -> type -> expr -> expr
| DynCall : expr -> id -> expr -> expr
| SubCast : type -> expr -> expr
| BehCast : type -> expr -> expr
| New : id -> list expr -> expr.

Inductive fd :=
| Field : id -> type -> fd.
Inductive md :=
| Method : id -> id -> type -> type -> expr -> md.
Inductive k :=
| ClassDef : id -> list fd -> list md -> k.
Definition ct := list k.

Inductive mt :=
| MType : id -> type -> type -> mt.

Fixpoint fields (C:id)(k:ct) :=
  match k with
  | (ClassDef D fds mds)::r =>
    match Nat.eqb C D with
      true => fds
    | false => fields C r
    end
  | nil => nil
  end.

Fixpoint methods (C:id)(k:ct) :=
  match k with
  | (ClassDef D fds mds)::r =>
    match Nat.eqb C D with
      true => mds
    | false => methods C r
    end
  | nil => nil
  end.

Inductive Subtype : list (id * id) -> ct -> type -> type -> Prop :=
| STRefl : forall m k t, Subtype m k t t
| STSeen : forall m k t1 t2, In (t1, t2) m ->
                             Subtype m k (class t1) (class t2)
| STClass : forall m m' k c d, m' = (c,d)::m -> Md_Subtypes m k (methods c k) (methods d k) ->
                               Subtype m k (class c) (class d)
with Md_Subtypes : list (id * id) -> ct -> list md -> list md -> Prop :=
     | MDCons : forall m x x' t1 t1' t2 t2' e e' mu k r mds,
         (In (Method m x' t1' t2' e') mds) ->
         (Subtype mu k t1' t1) -> (Subtype mu k t2 t2') ->
         (Md_Subtypes mu k mds ((Method m x t1 t2 e)::r))
     | MDNil : forall mu k mds, (Md_Subtypes mu k mds nil).
Scheme subtyping_ind := Induction for Subtype Sort Prop
with md_subtypings_ind := Induction for Md_Subtypes Sort Prop.

Hint Constructors Subtype.
Hint Constructors Md_Subtypes.

Inductive HasType : env -> heap -> ct -> expr -> type -> Prop :=
| KTSUB : forall g s k e t tp, HasType g s k e tp -> Subtype nil k tp t -> HasType g s k e t
| KTEXPR : forall g s k e t, HasTypeExpr g s k e t -> HasType g s k e t
with HasTypeExpr : env -> heap -> ct -> expr -> type -> Prop :=
| KTVAR : forall g s k x t, In (x,t) g -> HasTypeExpr g s k (Var x) t
| KTREAD : forall g s k f t C,
    In (this,(class C)) g ->
    In (Field f t) (fields C k) ->
    HasTypeExpr g s k (GetF (Var this) f) t
| KTREFREAD : forall g s k f a a' C t,
    In (a, HCell(C, a')) s ->
    In (Field f t) (fields C k) ->
    HasTypeExpr g s k (GetF (Ref a) f) t
| KTWRITE : forall g s k f e C t,
    In (this, (class C)) g ->
    In (Field f t) (fields C k) ->
    HasType g s k e t ->
    HasTypeExpr g s k (SetF (Var this) f e) t
| KTREFWRITE : forall g s k f a a' C e t,
    In (a, HCell(C, a')) s ->
    In (Field f t) (fields C k) ->
    HasType g s k e t ->
    HasTypeExpr g s k (SetF (Ref a) f e) t
| KTCALL : forall g s k m t t' e e' eb x C,
    HasType g s k e (class C) ->
    HasType g s k e' t ->
    In (Method m x t t' eb) (methods C k) ->
    HasTypeExpr g s k (Call e m t t' e') t'
| KTDYNCALL : forall g s k e e' m,
    HasType g s k e Any ->
    HasType g s k e' Any ->
    HasTypeExpr g s k (DynCall e m e') Any
| KTNEW : forall g s k C es fds mds,
    HasTypes g s k es fds ->
    In (ClassDef C fds mds) k ->
    HasTypeExpr g s k (New C es) (class C)
| KTSUBCAST : forall g s k e t tp,
    HasType g s k e tp ->
    HasTypeExpr g s k (SubCast t e) t
| KTBEHCAST : forall g s k e t tp,
    HasType g s k e tp ->
    HasTypeExpr g s k (BehCast t e) t
| KTREFTYPE : forall g s k a C t a',
    In (a,(HCell(C,a'))) s ->
    Subtype nil k (class C) t ->
    HasTypeExpr g s k (Ref a) t
| KTREFANY : forall g s k a,
    HasTypeExpr g s k (Ref a) Any
with HasTypes : env -> heap -> ct -> list expr -> list fd -> Prop :=
     | HTSCONS : forall g s k e t f er fr,
         HasType g s k e t ->
         HasTypes g s k er fr -> 
         HasTypes g s k (e::er) ((Field f t)::fr)
     | HTSNIL : forall g s k, HasTypes g s k nil nil.

Scheme typing_ind := Induction for HasType Sort Prop
                     with expr_typing_ind := Induction for HasTypeExpr Sort Prop
                                             with typings_ind := Induction for HasTypes Sort Prop.

Hint Constructors HasType.
Hint Constructors HasTypes.
Hint Constructors HasTypeExpr.

Lemma env_weakening : forall g g' s k e t,
    HasType g s k e t -> HasType (g ++ g') s k e t.
Proof.
  intros. apply typing_ind with
          (P:=fun g => fun s => fun k => fun e0 => fun t => fun ih => HasType (g ++ g') s k e0 t)
            (P0:=fun g s k e0 t ih => HasTypeExpr (g ++ g') s k e0 t)
            (P1:=fun g => fun s => fun k => fun es0 => fun fds => fun ih => HasTypes (g ++ g') s k es0 fds)
            (e:=g); try eauto.
  - intros. eapply KTVAR. apply in_app_iff. auto.
  - intros. eapply KTREAD; eauto. apply in_app_iff. eauto.
  - intros. eapply KTWRITE; eauto. apply in_app_iff. eauto.
Qed.

Lemma heap_weakening : forall g s s' k e t,
    HasType g s k e t -> HasType g (s ++ s') k e t.
Proof.
  intros. apply typing_ind with
          (P:=fun g => fun s => fun k => fun e0 => fun t => fun ih => HasType g (s ++ s') k e0 t)
            (P0 := fun g s k e0 t ih => HasTypeExpr g (s ++ s') k e0 t)
            (P1:=fun g => fun s => fun k => fun es0 => fun fds => fun ih => HasTypes g (s ++ s') k es0 fds); try eauto.
  - intros. eapply KTREFREAD; eauto. apply in_app_iff. eauto.
  - intros. eapply KTREFWRITE; eauto. apply in_app_iff. eauto.
  - intros. eapply KTREFTYPE; eauto. apply in_app_iff. eauto.
Qed.

Lemma mu_weakening : forall mu mu' k t1 t2,
  Subtype mu k t1 t2 -> Subtype (mu ++ mu') k t1 t2.
Proof. 
  intros. apply subtyping_ind with
          (P := fun mu => fun k => fun t1 => fun t2 => fun ih => Subtype (mu ++ mu') k t1 t2)
            (P0 := fun mu => fun k => fun mds1 => fun mds2 => fun ih => Md_Subtypes (mu ++ mu') k mds1 mds2); try eauto.
  intros. apply STSeen. apply in_app_iff. eauto.
Qed.

Lemma subtype_transitive : forall mu k t1 t2 t3,
  Subtype mu k t1 t2 -> Subtype mu k t2 t3 -> Subtype mu k t1 t3. 
Admitted. 

Fixpoint subst(thisref : ref)(varref : ref)(var : id)(exp : expr) :=
  match exp with
  | Var x => match Nat.eqb x this, Nat.eqb x var with
             | true, _ => Ref thisref
             | _, true => Ref varref
             | _, _ => Var x
             end
  | Ref a => Ref a
  | GetF e f => GetF (subst thisref varref var e) f
  | SetF e f e' => SetF (subst thisref varref var e) f (subst thisref varref var e')
  | Call e m t1 t2 e' => Call (subst thisref varref var e) m t1 t2 (subst thisref varref var e')
  | DynCall e m e' => DynCall (subst thisref varref var e) m (subst thisref varref var e')
  | SubCast t e => SubCast t (subst thisref varref var e)
  | BehCast t e => BehCast t (subst thisref varref var e)
  | New C es => New C (List.map (subst thisref varref var) es)
  end.

Lemma eventually_concrete : forall g s k e t,
  HasType g s k e t -> exists tp, Subtype nil k tp t /\ HasTypeExpr g s k e tp.
Proof.
  intros. induction H.
  - inversion IHHasType as [t' (H1, H2)]. exists t'. split.
    + apply subtype_transitive with (t2 := tp); try eauto.
    + apply H2.
  - exists t. split; eauto.
Qed.


Require Import Coq.Program.Equality.
Lemma substituion_typing : forall C x t t' s k e a al a',
    x <> this -> 
    HasType ((this, (class C)) :: (x, t') :: nil) s k e t ->
    In (a,HCell(C,al)) s ->
    HasType nil s k (Ref a') t' ->
    HasType nil s k (subst a a' x e) t.
Proof.
  intros C x t t' s k e a al a'. intros.
  assert (Hduh1: ((this, (class C)) :: (x, t') :: nil) =((this, (class C)) :: (x, t') :: nil)).
  { reflexivity. }
  assert (Hduh2: s = s).
  { reflexivity. }
  assert (Hduh3: k = k).
  { reflexivity. }
  generalize dependent Hduh3. generalize dependent Hduh2. generalize dependent Hduh1.
  apply typing_ind with
  (P := fun g' s' k' e t => fun (ih : HasType g' s' k' e t) =>
                              g' = ((this, (class C)) :: (x, t') :: nil) ->
                              s' = s -> k' = k -> HasType nil s k (subst a a' x e) t)
    (P0 := fun g' s' k' e t ih => g' = ((this, (class C)) :: (x, t') :: nil) ->
                                  s' = s -> k' = k -> HasTypeExpr nil s k (subst a a' x e) t)
    (P1 := fun g' s' k' es ts ih => g' = ((this, (class C)) :: (x, t') :: nil) ->
                                    s' = s -> k' = k -> HasTypes nil s k (List.map (subst a a' x) es) ts);
    intros; subst; try eauto; try (inversion i); try (simpl; eauto).
  - destruct (x0 =? this) eqn:Hxthis.
    + apply Nat.eqb_eq in Hxthis. subst. inversion H3. subst. eauto.
    + destruct (x0 =? x) eqn:Hxx0.
      * apply Nat.eqb_eq in Hxx0. subst. inversion H3. subst. contradiction.
      * inversion H3. subst. apply Nat.eqb_neq in Hxthis. contradiction.
  - destruct (x0 =? this) eqn:Hxthis.
    + apply Nat.eqb_eq in Hxthis. subst. inversion H3. 
      * inversion H4. subst. contradiction.
      * inversion H4.
    + apply Nat.eqb_neq in Hxthis. inversion H3.
      * inversion H4. subst. destruct (x0 =? x0) eqn:Hxx.
        ** apply eventually_concrete in H2. inversion H2 as [t' (H5, H6)].
           inversion H6; subst. 
           **** eapply KTREFTYPE with (C:=C0); eauto. apply subtype_transitive with (t2 := t'); eauto.
           **** inversion H5. subst. apply KTREFANY. 
        ** apply Nat.eqb_neq in Hxx. inversion H3; contradiction.
      * inversion H4.
  - inversion H3. subst. eapply KTREFREAD; eauto.
  - inversion H3.
    + inversion H4. subst. contradiction.
    + inversion H4.
  - inversion H4. subst. eapply KTREFWRITE; eauto.
  - inversion H4.
    + inversion H5. contradiction.
    + inversion H5.
Qed.

Inductive WellFormedType : ct -> type -> Prop :=
| WFWA : forall k, WellFormedType k Any
| WFWTC : forall k C fds mds, In (ClassDef C fds mds) k -> WellFormedType k (class C).

Inductive WellFormedField : ct -> fd -> Prop :=
| WFFWF : forall f k t, WellFormedType k t -> WellFormedField k (Field f t).

Inductive WellFormedMethod : env -> heap -> ct -> md -> Prop :=
| WFMDUT : forall x g s k e m, HasType ((x,Any)::g) s k e Any -> WellFormedMethod g s k (Method m x Any Any e)
| WFMT : forall g s k C1 C2 x e m, WellFormedType k (class C1) -> WellFormedType k (class C2) ->
         HasType ((x,(class C1)) :: g) s k e (class C2) ->
         WellFormedMethod g s k (Method m x (class C1) (class C2) e).

Inductive WellFormedClass : heap -> ct -> k -> Prop :=
| WFWC : forall s k C mds fds, (forall fd, In fd fds -> WellFormedField k fd) ->
                     (forall md, In md mds -> WellFormedMethod ((this, class C) :: nil) s k md) ->
                       WellFormedClass s k (ClassDef C fds mds).

Inductive FieldRefWellFormed : ct -> heap -> list fd -> list ref -> Prop :=
| FRWF_Cons : forall k s f t fds a a', HasType nil s k (Ref a) t -> FieldRefWellFormed k s ((Field f t)::fds) (a::a')
| FRWF_Nil : forall k s, FieldRefWellFormed k s nil nil.

Inductive WellFormedHeap : ct -> heap -> Prop :=
| WFH : forall k s, (forall a' C al, In (a', HCell(C,al)) s ->
                                  (exists fds mds, (In (ClassDef C fds mds) k) /\ FieldRefWellFormed k s fds al)) ->
               WellFormedHeap k s.
                   
Inductive WellFormedState : ct -> expr -> heap -> Prop :=
| WFSWP : forall k e s t, HasType nil s k e t -> WellFormedHeap k s ->
          (forall ki, In ki k -> WellFormedClass s k ki) ->
          WellFormedState k e s.
 