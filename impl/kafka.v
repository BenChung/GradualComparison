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
         (Subtype mu k t1 t1') -> (Subtype mu k t2' t2) -> (Md_Subtypes mu k mds r) -> 
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
| KTREFANY : forall g s k a hc,
    In (a,hc) s -> 
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
  - intros. eapply KTREFANY; eauto. apply in_app_iff. eauto.
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

Lemma subtype_method_containment : forall k C D md,
    Subtype nil k (class C) (class D) -> In md (methods D k) ->
    exists md', In md' (methods C k) /\ Md_Subtypes nil k (md'::nil) (md::nil).
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
           **** inversion H5. subst. eapply KTREFANY; eauto.
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
| WFMDUT : forall x g s k e m, x <> this ->
                               HasType (g ++ (x,Any)::nil) s k e Any ->
                               WellFormedMethod g s k (Method m x Any Any e)
| WFMT : forall g s k C1 C2 x e m,
    x <> this ->
    WellFormedType k (class C1) -> WellFormedType k (class C2) ->
    HasType (g ++ (x,(class C1))::nil) s k e (class C2) ->
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

Inductive NoDupsClasses : list k -> Prop :=
| NDUPK : forall C fds mds ks, NoDupsClasses ks -> (forall fds' mds', ~(In (ClassDef C fds' mds') ks)) ->
          NoDupsClasses ((ClassDef C fds mds)::ks).

Inductive WellFormedClass : heap -> ct -> k -> Prop :=
| WFWC : forall s k C mds fds,
    (forall fd, In fd fds -> WellFormedField k fd) ->
    (forall md, In md mds -> WellFormedMethod ((this, class C) :: nil) s k md) ->
    NoDupsFds fds -> NoDupsMds mds -> 
    WellFormedClass s k (ClassDef C fds mds).

Inductive WellFormedClassTable : heap -> ct -> Prop :=
| WFCT : forall s k,
    (forall C fds mds, In (ClassDef C fds mds) k -> WellFormedClass s k (ClassDef C fds mds)) ->
    NoDupsClasses k ->
    WellFormedClassTable s k.

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
          WellFormedClassTable s k ->
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

Lemma fields_gets_fields : forall C s k fds, 
    WellFormedType k (class C) -> WellFormedClassTable s k ->
    fields C k = fds <-> exists mds, In (ClassDef C fds mds) k.
Proof.
  intros C s k fds H H0. destruct H0 as [s k _ Hdups]. split; intros H1. 
  - induction k as [n | k''].
    + inversion H. subst. inversion H3.
    + destruct k'' as [C' fds' mds']. simpl in H1. destruct (Nat.eqb C C') eqn:HCC.
      * apply Nat.eqb_eq in HCC. subst. exists mds'. simpl. auto. 
      * apply Nat.eqb_neq in HCC. simpl. inversion H. subst. apply strong_weakening_of_type_wf in H; eauto. 
        apply IHk in H; eauto.
        ** inversion H as [mds'' H5]. exists mds''. auto.
        ** inversion Hdups. apply H2. 
  - induction k as [|k''].
    + inversion H1. inversion H0. 
    + destruct k'' as [C' fds' mds']. unfold fields. destruct (C =? C') eqn:HCC.
      * apply Nat.eqb_eq in HCC. subst. inversion H1. inversion H0.
        ** subst. inversion H2.
           *** inversion H2. subst. reflexivity.
        ** inversion Hdups. subst. apply H8 in H2. tauto.
      * apply IHk.
        ** eapply strong_weakening_of_type_wf; eauto. apply Nat.eqb_neq in HCC. apply HCC.
        ** inversion Hdups. tauto. 
        ** inversion H1. inversion H0.
           *** inversion H2. apply Nat.eqb_neq in HCC. symmetry in H5. subst. contradiction.
           *** exists x. eauto. 
Qed.

Lemma heap_wf_field_access : forall k s a C aps f t a',
    WellFormedHeap k s ->
    WellFormedClassTable s k ->
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
    WellFormedClassTable s k ->
    In (ClassDef C fds mds) k ->
    fds = (fields C k) ->
    NoDupsFds fds.
Proof.
  intros s k k' C fds mds H H0 H1. inversion H.
  apply H2 in H0. inversion H0. subst. apply H13.
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
    WellFormedClassTable s k -> In (ClassDef C fds mds) k -> In (ClassDef C fds' mds') k ->
    fds = fds' /\ mds = mds'.
Proof.
  intros. inversion H. subst. clear H2. clear H. induction k0.
  - inversion H0.
  - inversion H0; inversion H1.
    + subst. inversion H2. eauto.
    + subst. inversion H3. subst. apply H8 in H2. tauto.
    + inversion H3. subst. inversion H4. subst. apply H7 in H. tauto.
    + apply IHk0; eauto. inversion H3. apply H6.
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
  - intros. eapply KTREFANY. apply in_or_app. eauto.
Qed.

Lemma subtype_only_classes : forall mu k C t, Subtype mu k (class C) t -> exists D, t = (class D).
Proof.
  intros. inversion H.
  - exists C. reflexivity. 
  - subst. exists t2. reflexivity.
  - subst. exists d. reflexivity.
Qed.


Require Import Coq.Program.Tactics.
Definition retains_references(s1:heap)(s2:heap) :=
  forall a C aps, In (a, HCell(C,aps)) s1 -> exists aps', In(a, HCell(C,aps')) s2.

Lemma heapwrite_retains_refs' : forall a aps' s s',
    HeapWrite a aps' s s' -> retains_references s s'.
Proof.
  intros. induction H.
  - unfold retains_references. intros. destruct (Nat.eq_dec C0 C); destruct (Nat.eq_dec a0 a).
    + subst. exists aps. apply in_eq.
    + subst. inversion H.
      * exists aps. inject H0. tauto.
      * exists aps0. apply in_cons. tauto.
    + subst. inversion H.
      * inject H0. exists aps. tauto.
      * exists aps0. apply in_cons. tauto.
    + inversion H.
      * inject H0. tauto.
      * exists aps0. apply in_cons. tauto.
  - unfold retains_references. intros. inversion H1.
    + inject H2. exists aps0. apply in_eq.
    + unfold retains_references in IHHeapWrite.
      apply IHHeapWrite in H2. destruct H2. exists x. apply in_cons. apply H2. 
Qed.

Lemma retain_references_ref : forall s, retains_references s s.
Proof.
  intros. unfold retains_references; intros. exists aps. apply H.
Qed.
Hint Resolve retain_references_ref.


Lemma hastype_ignores_heapv'' : forall s s' k g e t,
    HasType g s k e t -> retains_references s s' -> HasType g s' k e t.
Proof.
  intros. 
  pose proof (eq_refl k0) as Hduh1.
  pose proof (eq_refl s) as Hduh2.
  generalize dependent Hduh1. generalize dependent Hduh2.
  apply typing_ind with
  (P:= fun g s'' k' e t ih => s'' = s -> k' = k0 -> HasType g s' k0 e t)
    (P0 := fun g s'' k' e t ih => s'' = s -> k' = k0 -> HasTypeExpr g s' k0 e t)
    (P1 := fun g s'' k' es ts ih => s'' = s -> k' = k0 -> HasTypes g s' k0 es ts);
    try (intros; subst; eauto; fail). 
  - intros. subst. unfold retains_references in H0. apply H0 in i. destruct i as [aps' H1]. eapply KTREFREAD; eauto.
  - intros. subst. unfold retains_references in H0. apply H0 in i. destruct i as [aps' H2]. eauto.
  - intros. subst. unfold retains_references in H0. apply H0 in i. destruct i as [aps' H1]. eauto.
  - intros. subst. unfold retains_references in H0. destruct hc.  destruct p.
    apply H0 in i. destruct i as [aps' H1]. eauto.
Qed.
Hint Resolve hastype_ignores_heapv''.

   
Lemma hastype_ignores_heapv : forall (k:ct) (s s':heap) g a a' aps' t,
    HasType g s k (Ref a) t ->
    HeapWrite a' aps' s s' -> 
    HasType g s' k (Ref a) t.
Proof.
  intros. eapply hastype_ignores_heapv''.  eauto. eapply heapwrite_retains_refs'; eauto.
Qed.
Hint Resolve hastype_ignores_heapv.

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

Lemma writing_keeps_refs : forall a a' s s' aps' C aps,
    In(a,HCell(C,aps)) s -> HeapWrite a' aps' s s' -> exists aps', In(a,HCell(C, aps')) s'.
Proof.
  intros. induction H0.
  - inversion H.
    + inversion H0. subst. exists aps0. apply in_eq.
    + exists aps. apply in_cons. apply H0.
  - inversion H.
    + inversion H2. subst. exists aps. apply in_eq.
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
    WellFormedClassTable s k ->
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
  pose proof (fields_gets_fields C s k fds H1 Hwfct). symmetry in Heqfds. pose proof Heqfds.
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
| SCall : forall a C aps s m x t1 t1' t2 t2' e k a',
    In (a, HCell(C,aps)) s ->
    In (Method m x t1 t2 e) (methods C k) ->
    Subtype nil k t1' t1 ->
    Subtype nil k t2 t2' ->
    Steps k (Call (Ref a) m t1' t2' (Ref a')) s k (subst a a' x e) s
| SDynCast : forall k a s, Steps k (SubCast Any (Ref a)) s k (Ref a) s
| SSubCast : forall a aps C D s k,
    In (a, HCell(C,aps)) s ->
    Subtype nil k (class C) (class D) ->
    Steps k (SubCast (class D) (Ref a)) s k (Ref a) s
| SCtx : forall k e s e' s' E,
    Steps k e s k e' s' -> Steps k (equivExpr e E) s k (equivExpr e' E) s'.
Hint Constructors Steps.
Hint Constructors EvalCtx.

Fixpoint typesof(fds : list fd) : list type :=
  match fds with
    (Field f t) :: r => t :: (typesof r)
  | nil => nil
  end.

Hint Constructors WellFormedState.


Lemma infields_implies_fieldin : forall k f s t a C aps,
    WellFormedHeap k s ->
    WellFormedClassTable s k ->
    In (a, HCell(C,aps)) s -> 
    In (Field f t) (fields C k) -> exists a', FieldIn f t a' (fields C k) aps.
Proof.
  intros. destruct H. apply H3 in H1. clear H3. destruct H1. remember (fields C k0) as fds.
  pose proof (fields_gets_fields C s k0 fds H1 H0). destruct H4. clear H5. symmetry in Heqfds.
  pose proof Heqfds as Heqfds'. apply H4 in Heqfds. destruct Heqfds as [mds Hin]. clear H4. symmetry in Heqfds'.
  pose proof (FieldsNoDupsFds s k0 k0 C fds mds H0 Hin Heqfds').
  clear Heqfds'. clear Hin H0 H1. clear mds H.
  induction H3.
  - destruct (Nat.eq_dec f f0); subst.
    + inject H2.
      * inject H0. exists a0. apply FieldIn_Here.
      * inject H4. apply H7 in H0. tauto.
    + inject H2.
      * inject H0. tauto.
      * inject H4. destruct (IHFieldRefWellFormed H0 H5) as [a0' H8].
        exists a0'. apply FieldIn_Next; eauto.
  - inversion H2.
Qed.

Fixpoint update_field_ref(f:id)(a:ref)(fds:list fd)(aps:list ref) : list ref :=
  match fds, aps with
    (Field f' t)::fr, a'::ar => match Nat.eqb f f' with
                                    true => a :: ar
                                  | false => a' :: (update_field_ref f a fr ar)
                                  end
  | _, _ => nil
  end.

Lemma update_field_is_well_formed : forall f t a k s aps aps' fds,
    FieldRefWellFormed k s fds aps ->
    (In (Field f t) fds) ->
    update_field_ref f a fds aps = aps' ->
    FieldWrite f a aps fds aps'.
Proof.
  intros. subst. induction H.
  - unfold update_field_ref. destruct (f =? f0) eqn:Hff.
    + apply Nat.eqb_eq in Hff. subst. apply FWC.
    + apply FWN.
      * apply Nat.eqb_neq. eauto.
      * apply IHFieldRefWellFormed; eauto. inversion H0; eauto. inject H2. apply Nat.eqb_neq in Hff.
        tauto.
  - inversion H0.
Qed.

Fixpoint update_heap(a:ref)(aps:list ref)(s:heap) : heap :=
  match s with
  | (a',HCell(C,aps'))::ar => match Nat.eqb a a' with
                                true => (a,HCell(C,aps))::ar
                              | false => (a',HCell(C,aps'))::(update_heap a aps ar)
                              end
  | nil => nil
  end.
Lemma update_heap_writes : forall s a C aps aps',
  (In (a,HCell(C, aps')) s) ->
  HeapWrite a aps s (update_heap a aps s).
Proof.
  intros. induction s.
  - inversion H.
  - unfold update_heap. destruct a0 as [a' [(C', aps'')]]. destruct (a =? a') eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. apply HWC.
    + apply Nat.eqb_neq in Heq. apply HWNC; eauto. apply IHs. inject H; eauto. inject H0. tauto.
Qed.

Lemma hastype_ignores_heapv' : forall (k : ct) (s s' : heap) (g : env)
                                      (a' : id) (aps' : list ref) (t : type) e,
    HasType g s k e t ->
    HeapWrite a' aps' s s' -> HasType g s' k e t.
Proof.
  intros. eapply hastype_ignores_heapv''. eauto. eapply heapwrite_retains_refs'. eauto.
Qed.

Lemma wfm_doesnt_care : forall md g s k s',
    WellFormedMethod g s k md ->
    retains_references s s' ->
    WellFormedMethod g s' k md.
Proof.
  intros. inject H.
  - apply WFMDUT; eauto. 
  - apply WFMT; eauto. 
Qed.

Lemma wfc_doesnt_care : forall s k c s',
  WellFormedClass s k c ->
  retains_references s s' ->
  WellFormedClass s' k c.
Proof.
  intros. inject H. eapply WFWC; eauto. intros. remember ((this, class C) :: nil) as g.
  apply H2 in H. eapply wfm_doesnt_care in H; eauto.
Qed.

Lemma wfct_doesnt_care : forall s s' k, 
  WellFormedClassTable s k ->
  retains_references s s' ->
  WellFormedClassTable s' k.
Proof.
  intros. inject H. apply WFCT.
  - intros. eapply wfc_doesnt_care; eauto.
  - eauto. 
Qed.


Lemma methods_in : forall fds mds s C k,
    WellFormedClassTable s k ->
    In (ClassDef C fds mds) k ->
    mds = (methods C k).
Proof.
  intros. destruct H as [s k _ H]. induction k.
  - inversion H0.
  - destruct a as [D fds' mds']. destruct (Nat.eq_dec C D).
    + subst. simpl. rewrite Nat.eqb_refl. inversion H0; eauto.
      * inject H1. reflexivity.
      * inject H. apply H7 in H1. tauto. 
    + unfold methods. apply Nat.eqb_neq in n. rewrite -> n. apply IHk.
      * inject H. apply H3.
      * inversion H0.
        ** inject H1. apply Nat.eqb_neq in n. tauto.
        ** apply H1.
Qed.
        
Lemma methods_are_wf : forall s k C mds,
    WellFormedClassTable s k ->
    WellFormedType k (class C) ->
  mds = (methods C k) ->
  (forall md, In md mds -> WellFormedMethod ((this, class C) :: nil) s k md).
Proof.
  intros. inversion H0. subst.
  pose proof (methods_in fds mds0 s C k0 H H5). rewrite <- H1 in H2. 
  inversion H. subst. 
  apply H3 in H5. clear H3 H4. inversion H5.
  subst. apply H9 in H2. eauto.  
Qed.

Lemma subtype_only_classes' : forall mu k t C,
    Subtype mu k t (class C) -> exists D, t = (class D).
Proof.
  intros. inversion H.
  - subst. exists C. reflexivity.
  - subst. exists t1. reflexivity.
  - eauto.
Qed.

Lemma deref_map : forall e1s a1s, 
    Deref e1s a1s -> e1s = map Ref a1s.
Proof.
  intros. induction H.
  - simpl. subst. reflexivity.
  - reflexivity.
Qed.

Fixpoint fresh_ref (s:heap)(i:nat) :=
  match s with
  | (a,hc)::r => match Nat.ltb a i with
                 | true => fresh_ref r i
                 | false => fresh_ref r (S a)
                 end
  | nil => i
  end.

Require Import Coq.omega.Omega.

Theorem fresh_not_in :
  forall s a a', a = fresh_ref s a' -> a' <= a /\ forall a'' hc, In(a'',hc) s -> a'' < a.
Proof.
  intros. generalize dependent a'. induction s.
  - intros. split.
    + unfold fresh_ref in H. omega.
    + intros. inversion H0.
  - intros.
    destruct a0 as [a'' hc]. unfold fresh_ref in H.
    destruct (Nat.ltb a'' a') eqn:Haa.
    + apply Nat.ltb_lt in Haa. apply IHs in H. destruct H. split.
      * omega.
      * intros. inversion H1.
        ** inject H2. omega.
        ** apply H0 in H2. omega.
    + apply Nat.ltb_ge in Haa. apply IHs in H. destruct H. split.
      * omega.
      * intros. inversion H1.
        ** inject H2. omega.
        ** apply H0 in H2.  omega.
Qed.

Theorem weakening_retains_refs: forall s s', retains_references s (s' ++ s).
Proof.
  intros. induction s.
  - unfold retains_references. intros. inversion H.
  - unfold retains_references. intros. inversion H.
    + exists aps. subst. apply in_or_app. right. apply in_eq.
    + exists aps. apply in_or_app. right. apply H.
Qed.

Lemma frwf_weakening : forall k s fts aps s',
    FieldRefWellFormed k s fts aps -> FieldRefWellFormed k (s' ++ s) fts aps.
Proof.
  intros. induction H.
  - apply FRWF_Cons.
    + apply heap_weakening_2. apply H.
    + apply IHFieldRefWellFormed. 
  - apply FRWF_Nil.
Qed.

Definition is_sound(k:ct)(s:heap)(e:expr)(t:type) :=
  (exists a : ref, e = Ref a) \/
  (exists (e' : expr) (s' : heap), Steps k e s k e' s' /\
                                           WellFormedState k e' s' /\
                                           HasType nil s' k e' t /\
                                           retains_references s s') \/
  (exists E : EvalCtx,
      (exists (a : ref) (m : id) (a' : ref),
          e = equivExpr (DynCall (Ref a) m (Ref a')) E) \/
      (exists (t' : type) (a : ref),
          e = equivExpr (SubCast t' (Ref a)) E)).


Theorem soundness: forall k e s t,
  WellFormedState k e s -> HasType nil s k e t -> is_sound k s e t.
Proof.
  intros k e s t Hwfs Hht. destruct Hwfs as [k e s _ _ Hwfh Hwfct].
  pose proof (eq_refl (@nil (id*type))) as Hduh0.
  pose proof (eq_refl k) as Hduh1. pose proof (eq_refl s) as Hduh2.    
  generalize dependent Hduh2. generalize dependent Hduh1. generalize dependent Hduh0.
  apply typing_ind with
  (P := fun g' s' k' e t ih =>
          g' = nil -> k' = k -> s' = s -> is_sound k s e t)
  (P0 := fun g' s' k' e t ih =>
           g' = nil -> k' = k -> s' = s -> is_sound k s e t)
  (P1 := fun g' s' k' es ts (ih : HasTypes g' s' k' es ts) => (* TODO: state IH for list of exprs *)
           g' = nil -> k' = k -> s' = s ->
           exists e1s (a1s : list ref) t1s e2s t2s,
             es = e1s ++ e2s /\
             ts = t1s ++ t2s /\
             FieldRefWellFormed k s t1s a1s /\
             Deref e1s a1s /\
             (forall e2, In e2 e2s -> forall a, e2 <> Ref a) /\
             @Forall2 expr type (is_sound k s) e2s (typesof t2s));
    try (intros; subst; inversion i; fail); try (intros; subst; unfold is_sound; eauto; fail). 
  - intros. subst. destruct H; eauto.
    + unfold is_sound. eauto.
    + unfold is_sound. right. destruct H.
      * left. destruct H  as [e' [s' [H1 [H2 [H3 H4]]]]]. exists e'. exists s'. repeat split; eauto.
      * right. eauto.
  - intros. subst. destruct H; try (unfold is_sound); eauto.
  - intros. subst. unfold is_sound. right. left.
    destruct (infields_implies_fieldin _ _ _ _ _ _ _ Hwfh Hwfct i i0) as [a'' H1].
    exists (Ref a''). exists s. repeat split; eauto.
    + eapply WFSWP; eauto. destruct Hwfh. apply a0 in i. destruct i as [_ H2].
      eapply FieldsWFImpliesFieldIn; eauto.
    + eapply FieldsWFImpliesFieldIn; eauto. destruct Hwfh. apply H0 in i.
      destruct i as [_ H2]. eauto. 
  - intros. subst. destruct H; eauto.
    * unfold is_sound. right. left. inject H.
      remember (fields C k) as fds.
      remember (update_field_ref f x fds a') as aps'.
      remember (update_heap a aps' s) as s'.
      exists (Ref x).
      exists s'. 
      assert (HHwrite: HeapWrite a aps' s s').
      { rewrite Heqs'. eapply update_heap_writes; eauto. }
      assert (HFwrite: FieldWrite f x a' fds aps').
      { eapply update_field_is_well_formed; eauto. destruct Hwfh. apply a0 in i.
        inject i. apply H0. }
      repeat split; try eauto.
      ** subst. eapply SWrite; eauto.
      ** eapply WFSWP; eauto.
         *** eapply write_field.
             **** apply Hwfh.
             **** apply Hwfct.
             **** apply h.
             **** rewrite Heqfds in i0. apply i0. 
             **** apply i.
             **** subst. apply HFwrite. 
             **** subst. apply HHwrite.
         *** eapply wfct_doesnt_care; eauto. eapply heapwrite_retains_refs'; eauto.
      ** eapply heapwrite_retains_refs'; eauto. 
    * unfold is_sound. right. inject H.
      ** left. destruct H0 as [e' [s' [HS [Hwfs [Hht' Hret]]]]].
         remember (EAssign a f (EHole)) as E.
         assert (Hleft: equivExpr e0 E = SetF (Ref a) f e0).
         { subst. reflexivity. }
         assert (Hright: equivExpr e' E = SetF (Ref a) f e').
         { subst. tauto. }
         rewrite <- Hleft.  exists (equivExpr e' E). exists s'. apply Hret in i. inversion i.
         repeat split; try eauto. 
         *** destruct Hwfs. eapply WFSWP; eauto.
             **** rewrite -> Hright. eapply KTEXPR. eapply KTREFWRITE; eauto.
         *** rewrite -> Hright. eapply KTEXPR. eapply KTREFWRITE; eauto.
      ** right. destruct H0 as [E H1]. remember (EAssign a f E) as E'.
         exists E'. subst. simpl. inversion H1.
         *** left. inversion H as [a1 [m1 [a2 H2]]]. exists a1. exists m1. exists a2.
             rewrite <- H2. reflexivity.
         *** right. inversion H as [t' [a1 H2]]. exists t'. exists a1. rewrite <- H2. reflexivity.
  - intros. subst. destruct H; destruct H0; eauto.
    + destruct H as [a1 H1]. destruct H0 as [a2 H2]. subst. apply eventually_concrete in h.
      unfold is_sound. right. left.
      destruct h as [tp [H1 H2]]. inversion H2; eauto.
      * subst. pose proof (subtype_transitive _ _ _ _ _ H6 H1).
        apply subtype_method_containment with (md0 := (Method m x t0 t' eb)) in H; eauto.
        inversion H as [[m' x' t0' t'' e'] [H3 H4]]. inversion H4. subst. inversion H13; eauto.
        ** inject H5. clear H18.
           remember (subst a1 a2 x'0 e'0) as ebody. exists ebody. exists s.
           assert (Hbody: HasType nil s k ebody t2').
           {
             pose proof H0 as Hback. inversion Hwfh. subst. apply H7 in H0. destruct H0.
             pose proof H0. inversion H0. subst. remember (methods C0 k) as mds'.
             pose proof (methods_are_wf s k C0 mds' Hwfct H9 Heqmds'). subst. apply H10 in H3.
             inversion H3.
             **** subst. simpl in H24. eapply substituion_typing; eauto. 
             **** subst. simpl in H26. eapply substituion_typing; eauto. 
           }
           repeat split; eauto.
           *** rewrite Heqebody. eapply SCall with (C:=C0)(aps := a'); eauto. 
        ** inversion H5.
      * subst. inversion H1.
    + destruct H as [a H]. subst. destruct H0.
      * unfold is_sound. right. left. inversion H as [e0' [s' [H1 [H2 [H3 H4]]]]].
        remember (ECall2 a m t0 t' EHole) as E.
        assert (Hleft: equivExpr e' E = Call (Ref a) m t0 t' e').
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = Call (Ref a) m t0 t' e0').
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) t').
        {
          rewrite Hright. apply KTEXPR. eapply KTCALL; eauto.
        }
         exists (equivExpr e0' E). exists s'.  repeat split; eauto.
        ** rewrite <- Hleft. eauto.
        ** eapply WFSWP; eauto.
           *** inversion H2. apply H5.
           *** eapply wfct_doesnt_care; eauto.
      * unfold is_sound. right. right. destruct H as [E H].
        remember (ECall2 a m t0 t' E) as E'. exists E'. inject H.
        ** left. inversion H0 as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           simpl. rewrite He. tauto.
        ** right. inversion H0 as [t'' [a' He]]. exists t''. exists a'. simpl.
           rewrite He. tauto.
    + destruct H.
      * inversion H as [e0' [s' [H1 [H2 [H3 H4]]]]]. unfold is_sound.
        right. left.
        remember (ECall1 EHole m t0 t' e') as E.
        assert (Hleft: equivExpr e0 E = (Call e0 m t0 t' e')).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = Call e0' m t0 t' e').
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) t').
        { rewrite Hright. apply KTEXPR. eapply KTCALL; eauto. }
        exists (equivExpr e0' E). exists s'. repeat split; eauto.
        ** rewrite<- Hleft. eapply SCtx. apply H1.
        ** eapply WFSWP; eauto.
           *** inversion H2. auto.
           ***  eapply wfct_doesnt_care; eauto.
      * destruct H as [E H]. remember (ECall1 E m t0 t' e') as E'.
        unfold is_sound. right. right. exists E'. clear H0. inject H.
        ** left. inversion H0 as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           subst. simpl. auto.
        ** right. inversion H0 as [t'' [a' He]]. exists t''. exists a'. subst. simpl. auto.
    + destruct H.
      * inversion H as [e0' [s' [H1 [H2 [H3 H4]]]]]. unfold is_sound.
        right. left.
        remember (ECall1 EHole m t0 t' e') as E.
        assert (Hleft: equivExpr e0 E = (Call e0 m t0 t' e')).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = Call e0' m t0 t' e').
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) t').
        { rewrite Hright. apply KTEXPR. eapply KTCALL; eauto. }
        exists (equivExpr e0' E). exists s'. repeat split; eauto.
        ** rewrite<- Hleft. eapply SCtx. apply H1.
        ** eapply WFSWP; eauto.
           *** inversion H2. auto.
           ***  eapply wfct_doesnt_care; eauto.
      * destruct H as [E H]. remember (ECall1 E m t0 t' e') as E'.
        unfold is_sound. right. right. exists E'. clear H0. inject H.
        ** left. inversion H0 as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           subst. simpl. auto.
        ** right. inversion H0 as [t'' [a' He]]. exists t''. exists a'. subst. simpl. auto.
  - intros. subst. destruct H; destruct H0; eauto.
    + unfold is_sound. right. right. exists EHole. left.
      inversion H. inversion H0. exists x. exists m. exists x0. simpl. subst.
      tauto.
    + destruct H0.
      * inversion H0 as [e0' [s' [H1 [H2 [H3 H4]]]]]. unfold is_sound.
        right. left. inversion H as [a]. subst. remember (EDCall2 a m EHole) as E.
        assert (Hleft: equivExpr e' E = (DynCall (Ref a) m e')).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = (DynCall (Ref a) m e0')).
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) Any).
        { subst. simpl. eapply KTEXPR. eapply KTDYNCALL; eauto. }
        exists (equivExpr e0' E). exists s'. repeat split; eauto.
        ** rewrite <- Hleft. eapply SCtx; eauto.
        ** eapply WFSWP; eauto.
           *** inversion H2; auto.
           *** eapply wfct_doesnt_care; eauto.
      * destruct H as [a H]. subst. destruct H0 as [E H0]. remember (EDCall2 a m E) as E'.
        unfold is_sound. right. right. exists E'. inject H0.
        ** left. inversion H as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           subst. eauto.
        ** right. inversion H as [t'' [a' He]]. exists t''. exists a'. subst. simpl. auto.
    + destruct H0 as [a H0]. subst. destruct H.
      * unfold is_sound. right. left. remember (EDCall1 EHole m (Ref a)) as E.
        inversion H as [e0' [s' [H1 [H2 [H3 H4]]]]].
        assert (Hleft: equivExpr e0 E = (DynCall e0 m (Ref a))).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = DynCall e0' m (Ref a)).
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) Any).
        { rewrite Hright. apply KTEXPR. eapply KTDYNCALL; eauto. }
        exists (equivExpr e0' E). exists s'. repeat split; eauto.
        ** rewrite <- Hleft. eapply SCtx; eauto.
        ** eapply WFSWP; eauto.
           *** inversion H2; auto.
           *** eapply wfct_doesnt_care; eauto.
      * unfold is_sound. right. right. destruct H as [E H]. remember (EDCall1 E m (Ref a)) as E'.
        exists E'. inversion H.
        ** left. inversion H0 as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           subst. auto.
        ** right. inversion H0 as [t'' [a' He]]. exists t''. exists a'. subst. simpl. auto.
    + clear H0. destruct H.
      * unfold is_sound. right. left. remember (EDCall1 EHole m e') as E.
        inversion H as [e0' [s' [H1 [H2 [H3 H4]]]]].
        assert (Hleft: equivExpr e0 E = (DynCall e0 m e')).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = DynCall e0' m e').
        { subst. tauto. }
        assert (Htyped: HasType nil s' k (equivExpr e0' E) Any).
        { rewrite Hright. apply KTEXPR. eapply KTDYNCALL; eauto. }
        exists (equivExpr e0' E). exists s'. repeat split; eauto.
        ** rewrite <- Hleft. eapply SCtx; eauto.
        ** eapply WFSWP; eauto.
           *** inversion H2; auto.
           *** eapply wfct_doesnt_care; eauto.
      * unfold is_sound. right. right. destruct H as [E H]. remember (EDCall1 E m e') as E'.
        exists E'. inversion H.
        ** left. inversion H0 as [a' [m' [a'' He]]]. exists a'. exists m'. exists a''.
           subst. auto.
        ** right. inversion H0 as [t'' [a' He]]. exists t''. exists a'. subst. simpl. auto.
  - intros. subst. destruct H as [e1s H]; eauto. destruct H as [a1s [t1s [e2s [t2s [H [H0 [H1 H2]]]]]]]. 
    induction e2s.
    + rewrite app_nil_r in H. subst. inversion H2. destruct t2s; eauto.
      * clear H2. unfold is_sound. right. left.
        remember (fresh_ref s 0) as a.
        remember (HCell(C,a1s)) as hc.
        remember ((a,hc)::s) as s'.
        exists (Ref a). exists s'. repeat split; eauto. 
        ** eapply SNew.
           *** unfold not. intros. apply fresh_not_in in Heqa. destruct Heqa.
               apply H4 in H2. omega.
           *** apply H.
           *** rewrite Heqs'. rewrite Heqhc. reflexivity.
        ** assert (Hndh: NoDupsHeap s').
           {
             rewrite Heqs'. apply NDH_Cons.
             ***** unfold not. intros.
             apply fresh_not_in in Heqa. destruct Heqa.
             apply H4 in H2. omega.
             ***** destruct Hwfh. apply H2.
           }
          eapply WFSWP; eauto.
           *** eapply KTEXPR. eapply KTREFTYPE.
               **** rewrite Heqs'. rewrite Heqhc. apply in_eq.
               **** apply STRefl.
           *** apply WFH.
               **** apply Hndh. 
               **** intros. destruct (Nat.eq_dec a0 a).
                    { pose proof (in_eq (a,hc) s). rewrite<- Heqs' in H3. rewrite e0 in H2.
                      pose proof (nodups_collapses_refs s' a hc (HCell(C0,aps)) Hndh H3 H2).
                      rewrite H4 in Heqhc. inversion Heqhc. 
                      split.
                      - eapply WFWTC; eauto. 
                      - rewrite app_nil_r in i.
                        pose proof (fields_gets_fields C s k t1s (WFWTC k C t1s mds i) Hwfct).
                        destruct H5.
                        assert (HFields: fields C k = t1s).
                        {
                          apply H8. exists mds. apply i.
                        }
                        rewrite HFields. rewrite Heqs'. apply frwf_weakening with (s':=(a,hc)::nil)(s:=s).
                        apply H1. 
                    }
                    {
                      rewrite Heqs' in H2. inversion H2.
                      - inversion H3. symmetry in H5. tauto. 
                      - clear H2. split.
                        + destruct Hwfh. apply H4 in H3. destruct H3 as [H3 H5].
                          eauto.
                        + destruct Hwfh. apply H4 in H3. destruct H3 as [H3 H5].
                          rewrite Heqs'. apply frwf_weakening with (s':=(a,hc)::nil). eauto. 
                    }
           *** eapply wfct_doesnt_care; eauto. rewrite Heqs'.
               apply weakening_retains_refs with (s' := (a,hc)::nil).
        ** apply KTEXPR. apply KTREFTYPE with (C:=C)(a':=a1s).
           *** rewrite Heqhc in Heqs'. rewrite Heqs'. apply in_eq.
           *** apply STRefl.
        ** rewrite Heqs'. apply weakening_retains_refs with (s':=(a,hc)::nil).
      * destruct H0. inversion H3. destruct f. discriminate.
    + destruct H2. destruct H3. clear IHe2s. unfold is_sound. right.
      inversion H4 as [|e' t' eps tps]. subst. inversion H5.
      * destruct H. unfold not in H3. rewrite H in H3. exfalso. eapply H3.
        ** apply in_eq.
        ** eauto.
      * destruct H.
        ** left. destruct H as [e' [s' [Hi1 [Hi2 [Hi3 Hi4]]]]].
           remember (ENew C a1s EHole e2s) as E.
           assert (Hleft: equivExpr a E = (New C (e1s ++ a :: e2s))).
           { subst. simpl. rewrite deref_map with (e1s:=e1s)(a1s:=a1s); eauto. }
           assert (Hright: equivExpr e' E = (New C (e1s ++ e' :: e2s))).
           { subst. simpl. rewrite deref_map with (e1s:=e1s)(a1s:=a1s); eauto. }
           assert (Htyped: HasType nil s' k (equivExpr e' E) (class C)).
           { subst. simpl. rewrite<- deref_map with (e1s:=e1s)(a1s:=a1s); eauto.
             eapply KTEXPR. eapply KTNEW; eauto.
Abort.