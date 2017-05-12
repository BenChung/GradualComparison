Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.

Definition id := nat.
Definition this:id := 0.
Definition ref := nat.
(* Cell = id [class] * [list of fields]  *)
Inductive Cell :=
| HCell : nat * list nat -> Cell.
(* pointer to an object *)
Definition heap := list (id * Cell).

Inductive type :=
| class : id -> type
| Any : type.
Definition env := list (id * type).

Inductive expr :=
| Var : id -> expr
| Ref : ref -> expr (* location of object *)
| GetF : expr -> id -> expr
| SetF : expr -> id -> expr -> expr
| Call : expr -> id -> type -> type -> expr -> expr
| DynCall : expr -> id -> expr -> expr
| SubCast : type -> expr -> expr (* <t> *)
| BehCast : type -> expr -> expr (* << t >>*)
| New : id -> list expr -> expr.

Inductive fd :=
| Field : id -> type -> fd.
Inductive md := (* M X t t e *)
| Method : id -> id -> type -> type -> expr -> md.
Inductive k :=
| ClassDef : id -> list fd -> list md -> k.
Definition ct := list k.

(*
Inductive mt :=
| MType : id -> type -> type -> mt.
*)

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
         (Subtype mu k t1' t1) -> (Subtype mu k t2 t2') -> (Md_Subtypes mu k mds r) -> 
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

(* [thisref/this][varref/var](exp) *)
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
(* s -- heap *)
Lemma substituion_typing : forall C x t t' s k e a al a',
    x <> this -> 
    (* method body is ok*)
    HasType ((this, (class C)) :: (x, t') :: nil) s k e t -> 
    (*  *)
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
      * apply Nat.eqb_eq in Hxx0. subst. inversion H3. subst. 
        assert (Heq : this = this) by reflexivity. contradiction.
      * inversion H3. subst. apply Nat.eqb_neq in Hxthis. 
        assert (Heq : this = this) by reflexivity. contradiction.
  - destruct (x0 =? this) eqn:Hxthis.
    + apply Nat.eqb_eq in Hxthis. subst. inversion H3. 
      * inversion H4. subst. 
        assert (Heq : this = this) by reflexivity. contradiction.
      * inversion H4.
    + apply Nat.eqb_neq in Hxthis. inversion H3.
      * inversion H4. subst. destruct (x0 =? x0) eqn:Hxx.
        ** apply eventually_concrete in H2. inversion H2 as [t' (H5, H6)].
           inversion H6; subst. 
           **** eapply KTREFTYPE with (C:=C0); eauto. apply subtype_transitive with (t2 := t'); eauto.
           **** inversion H5. subst. apply KTREFANY. 
        ** apply Nat.eqb_neq in Hxx. inversion H3; 
           assert (Heq : x0 = x0) by reflexivity; contradiction.
      * inversion H4.
  - inversion H3. subst. eapply KTREFREAD; eauto.
  - inversion H3.
    + inversion H4. subst. 
      assert (Heq : this = this) by reflexivity. contradiction.
    + inversion H4.
  - inversion H4. subst. eapply KTREFWRITE; eauto.
  - inversion H4.
    + inversion H5. assert (Heq : this = this) by reflexivity. contradiction.
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

Inductive NoDupsMds : list md -> Prop :=
| NDUPTC : forall m x C D e mds,
    NoDupsMds mds -> 
    (forall x' C' D' e', ~ In (Method m x' (class C') (class D') e') mds) ->
    NoDupsMds ((Method m x (class C) (class D) e)::mds)
| NDUPUT : forall m x e mds,
    NoDupsMds mds ->
    (forall x' e', ~In (Method m x' Any Any e') mds) ->
    NoDupsMds ((Method m x Any Any e)::mds)
| NDUPN : NoDupsMds nil.

Inductive NoDupsFds : list fd -> Prop :=
| NDUPFD : forall f t fds, NoDupsFds fds -> (forall t', ~ (In (Field f t') fds)) -> NoDupsFds ((Field f t)::fds).

Inductive WellFormedClass : heap -> ct -> k -> Prop :=
| WFWC : forall s k C mds fds,
    (forall fd, In fd fds -> WellFormedField k fd) ->
    (forall md, In md mds -> WellFormedMethod ((this, class C) :: nil) s k md) ->
    NoDupsFds fds -> NoDupsMds mds -> 
    WellFormedClass s k (ClassDef C fds mds).

Inductive WellFormedClassTable : heap -> ct -> ct -> Prop :=
| WFCTC : forall c C fds mds s k kr, 
    c = ClassDef C fds mds -> 
    (forall fd' md', ~In (ClassDef C fd' md') kr) ->
    (WellFormedClass s k c) -> WellFormedClassTable s k kr ->
    WellFormedClassTable s k (c::kr)
| WFNIL : forall s k, WellFormedClassTable s k nil.

Inductive FieldRefWellFormed : ct -> heap -> list fd -> list ref -> Prop :=
| FRWF_Cons : forall k s f t fds a a', HasType nil s k (Ref a) t ->
                                       FieldRefWellFormed k s fds a' ->
                                       FieldRefWellFormed k s ((Field f t)::fds) (a::a')
| FRWF_Nil : forall k s, FieldRefWellFormed k s nil nil.

Inductive NoDupsHeap : heap -> Prop :=
| NDH_Cons : forall s a hc', (forall hc, ~(In(a,hc) s)) -> NoDupsHeap s -> NoDupsHeap ((a,hc')::s)
| NDH_Nil : NoDupsHeap nil.

Inductive WellFormedHeap : ct -> heap -> Prop :=
| WFH : forall k s, NoDupsHeap s ->
                    (forall a C aps, In (a,HCell(C, aps)) s -> WellFormedType k (class C) /\ FieldRefWellFormed k s (fields C k) aps) ->
                    WellFormedHeap k s.       

Inductive WellFormedState : ct -> expr -> heap -> Prop :=
| WFSWP : forall k e s t, HasType nil s k e t -> WellFormedHeap k s ->
          WellFormedClassTable s k k ->
          WellFormedState k e s.

(* all exprs are refs in a list *)
Inductive Deref : list expr -> list ref -> Prop :=
| DREF_Cons : forall a es ais, Deref es ais -> Deref ((Ref a)::es) (a::ais)
| DREF_Nil : Deref nil nil.

Inductive FieldIn : id -> type -> ref -> list fd -> list ref -> Prop :=
| FieldIn_Next : forall f f' a a' fdr t t' ar,
    f <> f' -> FieldIn f t a fdr ar -> FieldIn f t a ((Field f' t') :: fdr) (a' :: ar)
| FieldIn_Here : forall f a t fdr ar, FieldIn f t a ((Field f t) :: fdr) (a :: ar).

Lemma FieldsWFImpliesFieldIn : forall k s fds aps f t a,
  FieldRefWellFormed k s fds aps -> FieldIn f t a fds aps -> HasType nil s k (Ref a) t.
Proof.
  intros k s fds aps f t a H1 H2. induction H1.
  - destruct (Nat.eqb f f0) eqn:Hf.
    + apply Nat.eqb_eq in Hf. subst. inversion H2; subst;
      try tauto; apply H.
    + apply Nat.eqb_neq in Hf. inversion H2; subst; try tauto.
      (*apply IHFieldRefWellFormed in H11. apply H11. assumption.*)
  - inversion H2.
Qed.

Lemma strong_weakening_of_type_wf : forall C C' fds mds k,
    WellFormedType ((ClassDef C' fds mds) :: k) (class C) -> C <> C' ->
    WellFormedType k (class C).
Proof.
  intros C C' fds mds k H1 H2. inversion H1; subst. inversion H3.
  - inversion H. symmetry in H4. contradiction.
  - eapply WFWTC. apply H.
Qed.

Lemma fields_gets_fields : forall C s k k' fds, 
    WellFormedType k (class C) -> WellFormedClassTable s k' k ->
    fields C k = fds <-> exists mds, In (ClassDef C fds mds) k.
Proof.
  intros C s k k' fds H H0. split; intros H1. 
  - induction k as [n | k''].
    + inversion H. subst. inversion H4.
    + destruct k'' as [C' fds' mds']. simpl in H1. destruct (Nat.eqb C C') eqn:HCC.
      * apply Nat.eqb_eq in HCC. subst. exists mds'. simpl. auto. 
      * apply Nat.eqb_neq in HCC. simpl. inversion H. subst. apply strong_weakening_of_type_wf in H; eauto. 
        apply IHk in H; eauto.
        ** inversion H as [mds'' H5]. exists mds''. auto.
        ** inversion H0. subst. eauto. 
  - induction k as [|k''].
    + inversion H1. inversion H2. 
    + destruct k'' as [C' fds' mds']. unfold fields. destruct (C =? C') eqn:HCC.
      * apply Nat.eqb_eq in HCC. subst. inversion H1. inversion H0.
        ** subst. inversion H2.
           *** inversion H3. subst. reflexivity. 
           *** inversion H5. subst. unfold not in H6. apply H6 in H3. contradiction.
      * apply IHk.
        ** eapply strong_weakening_of_type_wf; eauto. apply Nat.eqb_neq in HCC. apply HCC.
        ** inversion H0. eauto.
        ** inversion H1. inversion H2.
           *** inversion H3. apply Nat.eqb_neq in HCC. symmetry in H5. contradiction.
           *** exists x. eauto. 
Qed.

Lemma heap_wf_field_access : forall k s a C aps f t a',
    WellFormedHeap k s ->
    WellFormedClassTable s k k ->
    In (a, HCell(C, aps)) s -> FieldIn f t a' (fields C k) aps ->
  HasType nil s k (Ref a') t.
Proof.
  intros k s a C aps f t a' H0 H1 H2 H3. inversion H0. subst. apply H4 in H2. destruct H2 as [_ H2]. induction H2. 
  - destruct (Nat.eqb a0 a') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. inversion H3.
      * subst. apply IHFieldRefWellFormed; eauto.
      * subst. apply H2.
    + apply Nat.eqb_neq in Heq. inversion H3.
      * subst. apply IHFieldRefWellFormed; eauto.
      * subst. tauto.
  - inversion H3. 
Qed.

Inductive HeapWrite : id -> list ref -> heap -> heap -> Prop :=
| HWC : forall a aps C aps' s, HeapWrite a aps ((a,HCell(C,aps'))::s) ((a,HCell(C,aps)) :: s)
| HWNC : forall a a' aps aps' s s' C, a' <> a -> HeapWrite a aps s s' ->
         HeapWrite a aps ((a', HCell(C,aps')) :: s) ((a', (HCell(C,aps'))) :: s').

Inductive FieldWrite : id -> ref -> list ref -> list fd -> list ref -> Prop :=
| FWC : forall a f a' aps fs t, FieldWrite f a (a'::aps) ((Field f t)::fs) (a::aps)
| FWN : forall a f f' a' aps aps' fs t,
    f <> f' -> FieldWrite f a aps fs aps' -> FieldWrite f a (a'::aps) ((Field f' t)::fs) (a' :: aps').

Lemma FieldsNoDupsFds : forall s (k k' : ct) (C : id) fds mds, 
    WellFormedClassTable s k' k ->
    In (ClassDef C fds mds) k ->
    fds = (fields C k) ->
    NoDupsFds fds.
Proof.
  intros s k k' C fds mds H H0 H1. induction k.
  - inversion H0.
  - inversion H0.
    + inversion H. subst fds. subst.
      inversion H9. subst.  
      inversion H2.  rewrite <- H4. unfold fields.
      rewrite Nat.eqb_refl. apply H12.
    + apply IHk; eauto.
      * inversion H. subst. apply H10.
      * clear H1. clear IHk. clear H0. symmetry. rewrite fields_gets_fields with (s := s) (k' := k').
        ** exists mds. apply H2. 
        ** eapply WFWTC.  apply H2.
        ** inversion H. apply H8. 
Qed.

Lemma FieldWriteWellFormed : forall (k k' : ct) s a fds ais ais' t f,
    FieldRefWellFormed k s fds ais ->
    HasType nil s k (Ref a) t ->
    In (Field f t) fds ->
    NoDupsFds fds ->
    FieldWrite f a ais fds ais' ->
    FieldRefWellFormed k s fds ais'.
Proof.
  intros. induction H3.
  - inversion H1.
    + inversion H3. subst. apply FRWF_Cons; eauto.
      * inversion H. apply H12. 
    + inversion H2. subst. unfold not in H8. apply H8 in H3. contradiction.
  - apply FRWF_Cons.
    + inversion H. apply H9.
    + apply IHFieldWrite; eauto.
      * inversion H. apply H13.
      * inversion H1. 
        ** inversion H5. symmetry in H7. contradiction.
        ** apply H5.
      * inversion H2. apply H7.
Qed.

Lemma no_two_classes : forall s k C fds mds fds' mds',
    WellFormedClassTable s k k -> In (ClassDef C fds mds) k -> In (ClassDef C fds' mds') k ->
    fds = fds' /\ mds = mds'.
Proof.
  intros. induction H.
  - subst. destruct (Nat.eqb C C0) eqn:HCC.
    + apply Nat.eqb_eq in HCC. subst. inversion H0.
      * inversion H. subst. inversion H1.
        ** inversion H5. auto.
        ** apply H2 in H5. contradiction. 
      * apply H2 in H. contradiction.
    + apply Nat.eqb_neq in HCC. inversion H0.
      * inversion H. subst. tauto.
      * apply IHWellFormedClassTable in H.
        ** apply H.
        ** inversion H1.
           *** inversion H5. subst. tauto. 
           *** apply H5.
  - inversion H0. 
Qed.

Lemma heap_write_still_in : forall a s s' a' aps' hc,
  In (a, hc) s -> a <> a' -> HeapWrite a' aps' s s' -> In (a, hc) s'.
Proof.
  intros. induction H1.
  - inversion H.
    + inversion H1. subst. tauto. 
    + apply in_cons. apply H1. 
  - inversion H.
    + inversion H3. subst. apply in_eq. 
    + apply IHHeapWrite in H3.
      * apply in_cons. apply H3.
      * apply H0.
Qed.

Lemma nodupsheap_weakening : forall a hc s, NoDupsHeap ((a, hc)::s) -> NoDupsHeap s.
Proof.
  intros. inversion H. subst. apply H4.
Qed.

Lemma heap_write_now_in : forall a k s s' aps aps' C,
    WellFormedHeap k s -> In (a, HCell(C, aps)) s -> HeapWrite a aps' s s' -> In (a, HCell(C, aps')) s'.
Proof.
  intros. inversion H. subst. clear H3. clear H. induction H1.
  - destruct (Nat.eqb C C0) eqn:HCC.
    + apply Nat.eqb_eq in HCC. subst. apply in_eq.
    + apply Nat.eqb_neq in HCC. inversion H0.
      * inversion H. subst. tauto. 
      * inversion H2. subst. apply H4 in H. contradiction.
  - apply in_cons. apply IHHeapWrite.
    + inversion H0; eauto. inversion H3. subst. tauto.
    + apply nodupsheap_weakening in H2. apply H2.
Qed.

Lemma heap_weakening_2 : forall g s s' k e t, HasType g s k e t -> HasType g (s' ++ s) k e t.
Proof.
  intros g s s' k e t H.
  apply typing_ind with (P := fun g s k e t ih => HasType g (s' ++ s) k e t)
                          (P0 := fun g s k e t ih => HasTypeExpr g (s' ++ s) k e t)
                          (P1 := fun g s k es ts ih => HasTypes g (s' ++ s) k es ts); eauto.
  - intros. apply KTREFREAD with (a' := a') (C:=C).
    + apply in_or_app. right. eauto.
    + apply i0.
  - intros. apply KTREFWRITE with (a' := a') (C:=C); eauto.
    + apply in_or_app. eauto.
  - intros. apply KTREFTYPE with (a' := a') (C := C); eauto.
    apply in_or_app. eauto.
Qed.

Lemma subtype_only_classes : forall mu k C t, Subtype mu k (class C) t -> exists D, t = (class D).
Proof.
  intros. inversion H.
  - exists C. reflexivity. 
  - subst. exists t2. reflexivity.
  - subst. exists d. reflexivity.
Qed.
   
Lemma hastype_ignores_heapv : forall (k:ct) (s s':heap) a a' aps' t,
    WellFormedHeap k s ->
    HasType nil s k (Ref a) t ->
    HeapWrite a' aps' s s' -> 
    HasType nil s' k (Ref a) t.
Proof.
  intros.
  assert (Hduh: s' = s').
  { reflexivity. }
  assert (Hduh2: (Ref a) = (Ref a)).
  { reflexivity. }
  generalize dependent Hduh. generalize dependent Hduh2.
   (* pose proof typing_ind (fun g s k e t (ih : HasType g s k e t) => e = (Ref a) -> s = s' -> HasType nil s' k (Ref a) t). eapply H2. *)
  eapply typing_ind with (P := fun g s k e t (ih : HasType g s k e t) => e = (Ref a) -> s = s' -> HasType nil s' k (Ref a) t)
                           (P0 := fun g s k e t ih => e = (Ref a) -> s = s' -> HasTypeExpr nil s' k (Ref a) t)
                           (P1 := fun g s k es ts ih => True) (e:= nil); try (intros; subst; discriminate); eauto.
  - intros. subst. inversion H2. subst. eauto.
  - apply eventually_concrete in H0. destruct H0 as [tp [H2 H3]]. inversion H3.
    + subst. inversion H. subst. clear H H5. induction H1.
      * destruct (Nat.eqb a0 a) eqn:Heq.
        ** apply Nat.eqb_eq in Heq. subst. inversion H4.
           *** inversion H. subst. apply KTEXPR. eapply KTREFTYPE; eauto.
               **** apply in_eq.
               **** pose proof subtype_transitive (nil) k0 (class C) tp t H8 H2. apply H1. 
           *** inversion H0. apply H6 in H. tauto.
        ** apply Nat.eqb_neq in Heq. inversion H4.
           *** inversion H. subst. tauto.
           *** apply KTEXPR. eapply KTREFTYPE; eauto.
               **** apply in_cons. apply H.
               **** eapply subtype_transitive; eauto. 
      * destruct (Nat.eqb a' a) eqn:Heq.
        ** apply Nat.eqb_eq in Heq. subst. inversion H4.
           *** inversion H5. subst. apply KTEXPR. apply KTREFTYPE with (C:=C) (a' := a'0). 
               **** apply in_eq.
               **** eapply subtype_transitive; eauto.
           *** inversion H0. apply H9 in H5. tauto.
        ** apply Nat.eqb_neq in Heq. inversion H4.
           *** inversion H5. subst. tauto.
           *** apply heap_weakening_2 with (s' := (a',HCell(C0,aps')) :: nil). apply IHHeapWrite; eauto.
               **** apply nodupsheap_weakening in H0. apply H0.
    + subst. inversion H2. subst. apply KTEXPR. apply KTREFANY.
Qed.

Lemma fieldwf_still_good : forall k s a' s' fds aps' aps, 
  WellFormedHeap k s ->
  FieldRefWellFormed k s fds aps' ->
  HeapWrite a' aps s s' ->
  FieldRefWellFormed k s' fds aps'.
Proof.
  intros k s a s' fds aps' aps.
  intros Hwfh Hfrwf Hwrite.  
  induction Hfrwf.
  - apply FRWF_Cons.
    + eapply hastype_ignores_heapv; eauto.
    + apply IHHfrwf; eauto.
  - apply FRWF_Nil.
Qed.

Lemma writing_keeps_refs : forall a a' s s' aps' hc,
    In(a,hc) s -> HeapWrite a' aps' s s' -> exists hc', In(a,hc') s'.
Proof.
  intros. induction H0.
  - inversion H.
    + inversion H0. subst.  exists (HCell(C,aps)). apply in_eq.
    + exists hc. apply in_cons. apply H0.
  - inversion H.
    + inversion H2. subst. exists (HCell(C,aps')). apply in_eq.
    + apply IHHeapWrite in H2. inversion H2 as [hc' H3]. exists hc'.
      apply in_cons. apply H3.
Qed.

Lemma refs_still_not_in : forall a s a' aps' s',
  (forall hc, ~ (In(a,hc) s)) -> HeapWrite a' aps' s s' -> (forall hc', ~(In(a,hc') s')).
Proof.
  intros. destruct (Nat.eqb a a') eqn:Heq.
  + apply Nat.eqb_eq in Heq. subst. induction H0.
    * subst. exfalso. unfold not in H. eapply H.
      apply in_eq.
    * subst. unfold not. intros. inversion H2.
      ** inversion H3. subst. eapply H. apply in_eq.
      ** apply IHHeapWrite in H3; eauto. unfold not.
         intros. unfold not in H. eapply H. apply in_cons. apply H4.
  + apply Nat.eqb_neq in Heq. induction H0.
    * unfold not. intros. eapply H. inversion H0.
      ** inversion H1. subst. tauto. 
      ** apply in_cons. apply H1.
    * unfold not. intros. inversion H2.
      ** inversion H3. subst. eapply H. apply in_eq.
      ** apply IHHeapWrite.
         *** unfold not. intros. eapply H. apply in_cons. apply H4.
         *** apply Heq.
         *** apply H3.
Qed.

Lemma in_goes_backwards : forall a a' aps' s s' hc,
    (In(a,hc) s') -> HeapWrite a' aps' s s' -> a <> a' -> In(a,hc) s.
Proof.
  intros. induction H0.
  - destruct (Nat.eqb a a0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. tauto.
    + apply Nat.eqb_neq in Heq. inversion H; eauto.
      * inversion H0. subst. tauto.
      * apply in_cons. apply H0.
  - inversion H; eauto.
    + inversion H3. subst. apply in_eq.
    + apply in_cons. apply IHHeapWrite; eauto.
Qed.

Theorem nodupsheap_still_good: forall s a' aps' s',
  NoDupsHeap s -> HeapWrite a' aps' s s' -> NoDupsHeap s'.
Proof.
  intros. generalize dependent s'.
  induction H.
  - intros. destruct (Nat.eqb a' a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. inversion H1.
      * subst. apply NDH_Cons; eauto.
      * subst. apply IHNoDupsHeap in H9. apply NDH_Cons; eauto.
    + apply Nat.eqb_neq in Heq. inversion H1.
      * subst. tauto.
      * subst. apply IHNoDupsHeap in H9. apply NDH_Cons; eauto.
        inversion H1; subst; try tauto. eapply refs_still_not_in; eauto.
  - intros. inversion H0.
Qed.

Lemma nodups_first : forall a hc s, NoDupsHeap ((a,hc)::s) -> (forall hc', In (a,hc') ((a,hc)::s) -> hc = hc').
Proof.
  intros. inversion H. subst. inversion H0.
  - inversion H1. tauto.
  - apply H3 in H1. tauto.
Qed.

Lemma nodups_collapses_refs : forall s a hc hc',
    NoDupsHeap s -> In (a,hc) s -> In (a,hc') s -> hc = hc'.
Proof.
  intros.
  induction (H).
  - pose proof (Nat.eq_dec a a0). destruct H3; subst.
    + pose proof (nodups_first a0 hc'0 s H).
      apply H3 in H0. apply H3 in H1. subst. tauto.
    + inversion H0 as [H3|]; inversion H1 as [H4|]; try (inversion H3; inversion H4; subst).
      * tauto.
      * inversion H3. subst. tauto.
      * inversion H4. subst. tauto.
      * apply IHn; eauto.
  - inversion H0.
Qed.

Lemma fieldwf_implies_heapwf : forall k s s' a' C aps aps' fds,
  WellFormedHeap k s ->
  In (a', HCell(C,aps)) s ->
  fds = fields C k ->
  FieldRefWellFormed k s fds aps' ->
  HeapWrite a' aps' s s' ->
  WellFormedHeap k s'.
Proof.
  intros k s s' a C aps aps' fds.
  intros Hwfh Hin Hfields Hfieldswf Hwrite. inversion Hwfh. subst.
  apply WFH.
  - eapply nodupsheap_still_good; eauto.
  - intros. destruct (Nat.eqb a0 a) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. pose proof (heap_write_now_in _ _ _ _ _ _ _ Hwfh Hin Hwrite).
      assert (Hnds' : NoDupsHeap s').
      { eapply nodupsheap_still_good; eauto. }
      pose proof (nodups_collapses_refs s' a (HCell (C0, aps0)) (HCell (C, aps')) Hnds' H1 H2). inversion H3. subst. 
      split.
      { apply H0 in Hin. destruct Hin. eauto. }
      {
        eapply fieldwf_still_good.
        * apply Hwfh.
        * inversion H3. subst. apply Hfieldswf.
        * apply Hwrite.
      }
    + apply Nat.eqb_neq in Heq. eapply in_goes_backwards in H1; eauto. split.
      {
        apply H0 in H1. destruct H1. eauto.
      }
      {
        eapply fieldwf_still_good.
        * apply Hwfh.
        * eapply H0. eauto.
        * apply Hwrite.
      }
Qed.

Lemma write_field : forall s s' k a a' aps aps' t C f,
    WellFormedHeap k s ->
    WellFormedClassTable s k k ->
    HasType nil s k (Ref a) t ->
    In (Field f t) (fields C k) ->
    In (a', HCell(C, aps)) s ->
    FieldWrite f a aps (fields C k) aps' ->
    HeapWrite a' aps' s s' ->
    WellFormedHeap k s'.
Proof.
  intros s s' k a a' aps aps' t C f.
  intros Hwfh Hwfct Hht Hfin Hobj Hwrite Hhwrite.

  inversion Hwfh.
  subst. pose proof Hobj. apply H0 in H1. destruct H1. remember (fields C k) as fds.
  pose proof (fields_gets_fields C s k k fds H1 Hwfct). symmetry in Heqfds. pose proof Heqfds.
  apply H3 in Heqfds.
  destruct Heqfds as [mds H5]. 
    
  eapply fieldwf_implies_heapwf; eauto. eapply FieldWriteWellFormed; eauto.
  - inversion Hwfh. subst. eapply H0. apply Hobj.
  - rewrite-> H4. apply Hfin.
  - eapply FieldsNoDupsFds; eauto. subst. apply H5.
  - subst. apply Hwrite.
Qed.

Inductive EvalCtx :=
| EAssign : ref -> id -> EvalCtx -> EvalCtx
| ECall1 : EvalCtx -> id -> type -> type -> expr -> EvalCtx
| ECall2 : ref -> id -> type -> type -> EvalCtx -> EvalCtx
| EDCall1 : EvalCtx -> id -> expr -> EvalCtx
| EDCall2 : ref -> id -> EvalCtx -> EvalCtx
| ESubCast : type -> EvalCtx -> EvalCtx
| ENew : id -> list ref -> EvalCtx -> list expr -> EvalCtx
| EHole : EvalCtx.

Fixpoint equivExpr(ei:expr)(E:EvalCtx) :=
  match E with
  | EAssign a f E => SetF (Ref a) f (equivExpr ei E)
  | ECall1 E m t t' e => Call (equivExpr ei E) m t t' e
  | ECall2 a m t t' E => Call (Ref a) m t t' (equivExpr ei E)
  | EDCall1 E m e => DynCall (equivExpr ei E) m e
  | EDCall2 a m E => DynCall (Ref a) m (equivExpr ei E)
  | ESubCast t E => SubCast t (equivExpr ei E)
  | ENew C aps E ers => New C ((map Ref aps) ++ (equivExpr ei E)::ers)
  | EHole => ei
  end.

Inductive Steps : ct -> expr -> heap -> ct -> expr -> heap -> Prop :=
| SNew : forall a' s s' C k ais ais', (forall hc, ~ (In (a',hc) s)) ->
                                      Deref ais ais' ->
                                      s' = (a', HCell(C, ais'))::s ->
                                      Steps k (New C ais) s k (Ref a') s'
| SRead : forall a C t aps s k f a', 
    In (a, HCell(C, aps)) s ->
    FieldIn f t a' (fields C k) aps ->
    Steps k (GetF (Ref a) f) s k (Ref a') s
| SWrite : forall a C aps aps' s k f a' s',
    In (a, HCell(C,aps)) s ->
    FieldWrite f a' aps (fields C k) aps' ->
    HeapWrite a aps' s s' ->
    Steps k (SetF (Ref a) f (Ref a')) s k (Ref a') s'
| SCall : forall a C aps s m x t t' e k a',
    In (a, HCell(C,aps)) s ->
    In (Method m x t t' e) (methods C k) ->
    Steps k (Call (Ref a) m t t' (Ref a')) s k (subst a a' x e) s
| SDynCast : forall k a s, Steps k (SubCast Any (Ref a)) s k (Ref a) s
| SSubCast : forall a aps C D s k,
    In (a, HCell(C,aps)) s ->
    Subtype nil k (class C) (class D) ->
    Steps k (SubCast (class D) (Ref a)) s k (Ref a) s
| SCtx : forall k e s e' s' E,
    Steps k e s k e' s' -> Steps k (equivExpr e E) s k (equivExpr e' E) s'.
    