Require Import Coq.Setoids.Setoid.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Require Import Coq.Classes.EquivDec.
Require Import Coq.Program.Tactics.
Require Import Coq.MSets.MSets.
Require Import Coq.MSets.MSetList.
Require Import Coq.Structures.OrderedType.
Require Import Coq.Structures.OrdersEx.
Module Nat_Pair_OT := PairOrderedType(Nat_as_OT)(Nat_as_OT).
Module PairNatList := MSetList.Make(Nat_Pair_OT).


Definition id := nat.
Definition this:id := 0.
Definition that:id := 0.
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

Inductive ForallT {A : Type} (P : A -> Type) : list A -> Type :=
  ForallT_nil : ForallT P nil
| ForallT_cons : forall (x : A) (l : list A), P x -> ForallT P l -> ForallT P (x :: l).
Arguments ForallT_nil {_ _}.
Arguments ForallT_cons {_ _ _ _}.

Unset Elimination Schemes.

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

Definition expr_rect (P : expr -> Type) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)) :=
  fix F (e : expr) : P e :=
    match e as e0 return (P e0) with
    | Var i => f i
    | Ref r => f0 r
    | GetF e0 i => f1 e0 (F e0) i
    | SetF e0 i e1 => f2 e0 (F e0) i e1 (F e1)
    | Call e0 i t t0 e1 => f3 e0 (F e0) i t t0 e1 (F e1)
    | DynCall e0 i e1 => f4 e0 (F e0) i e1 (F e1)
    | SubCast t e0 => f5 t e0 (F e0)
    | BehCast t e0 => f6 t e0 (F e0)
    | New i l => f7 i l ((fix F' (l:list expr) : ForallT P l :=
                       match l with
                       | e :: r => ForallT_cons (F e) (F' r)
                       | nil => ForallT_nil 
                       end) l)
    end.

Definition expr_ind : forall (P : expr -> Prop) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)), forall e : expr, P e := expr_rect.

Definition expr_rec : forall (P : expr -> Set) (f : forall i : id, P (Var i)) (f0 : forall r : ref, P (Ref r))
           (f1 : forall e : expr, P e -> forall i : id, P (GetF e i))
           (f2 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (SetF e i e0))
           (f3 : forall e : expr, P e -> forall (i : id) (t t0 : type) (e0 : expr), P e0 -> P (Call e i t t0 e0))
           (f4 : forall e : expr, P e -> forall (i : id) (e0 : expr), P e0 -> P (DynCall e i e0))
           (f5 : forall (t : type) (e : expr), P e -> P (SubCast t e))
           (f6 : forall (t : type) (e : expr), P e -> P (BehCast t e))
           (f7 : forall (i : id) (l : list expr), ForallT P l -> P (New i l)), forall e : expr, P e := expr_rect.

Set Elimination Schemes.

Inductive fd :=
| Field : id -> type -> fd.
Inductive md := (* M X t t e *)
| Method : id -> id -> type -> type -> expr -> md.
Inductive k :=
| ClassDef : id -> list fd -> list md -> k.
Definition ct := list k.
Require Import Coq.Logic.FinFun.


Lemma type_dec : forall x y : type, {x = y} + {x <> y}.
Proof.
  decide equality; try (apply Nat.eq_dec).
Qed.
Ltac decideish_equality :=
  let foo x y :=
      try (unify x y; fail 1); 
      assert (Heqdec : {x = y} + {x <> y}) by eauto; destruct Heqdec as [Heq | Hneq];
      [subst|right; contradict Hneq; inject Hneq; reflexivity] in
  repeat match goal with
         | [ |- {?x = ?x} + {?x <> ?x}] => left; reflexivity
         | [ |- {?f ?x = ?g ?y} + {?f ?x <> ?g ?y}] => foo x y
         | [ |- {?f ?x _ = ?g ?y _} + {?f ?x _ <> ?g ?y _}] => foo x y
         | [ |- {?f ?x _ _ = ?g ?y _ _} + {?f ?x _ _ <> ?g ?y _ _}] => foo x y
         | [ |- {?f ?x _ _ _ = ?g ?y _ _ _} + {?f ?x _ _ _ <> ?g ?y _ _ _}] => foo x y
         | [ |- {?f ?x _ _ _ _ = ?g ?y _ _ _ _} + {?f ?x _ _ _ _ <> ?g ?y _ _ _ _}] => foo x y
         end.

Lemma expr_dec : EqDec expr.
Proof.
  pose proof Nat.eq_dec.
  pose proof type_dec.
  refine (expr_rec (fun x => forall y, {x = y} + {x <> y}) _ _ _ _ _ _ _ _ _);
    intros; try (destruct y); try solve [right; discriminate]; decideish_equality.
    - revert l0. induction l.
      + intros. destruct l0.
        * left. reflexivity.
        * right. discriminate.
      + intros. destruct l0.
        * right. discriminate.
        * inject H1. apply IHl with (l0 := l0) in H5. destruct H5.
          ** inject e0. specialize (H4 e). destruct H4.
             *** subst. eauto.
             *** right. contradict n. inject n. reflexivity.
          ** right. contradict n. inject n. reflexivity.
Qed.

Lemma md_dec : forall x y : md, {x = y} + {x <> y}.
Proof.
  decide equality; eauto using expr_dec, Nat.eq_dec, type_dec.
Qed.
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

Search Nat.eqb.

Fixpoint methods (C:id)(k:ct) :=
  match k with
  | (ClassDef D fds mds)::r =>
    match Nat.eqb C D with
      true => mds
    | false => methods C r
    end
  | nil => nil
  end.

Fixpoint method_def (m:id) (ms:list md) : (option md) :=
  match ms with
  | (Method m' x t1 t2 e)::r =>
    match Nat.eqb m m' with
    | true => Some(Method m' x t1 t2 e)
    | false => method_def m r
    end
  | nil => None
end.

Inductive Subtype : PairNatList.t -> ct -> type -> type -> Prop :=
| STRefl : forall m k t, Subtype m k t t
| STSeen : forall m k t1 t2, PairNatList.In (t1, t2) m ->
                             Subtype m k (class t1) (class t2)
| STClass : forall m m' k c d, m' = PairNatList.add (c,d) m ->
                               Md_Subtypes m' k (methods c k) (methods d k) ->
                               Subtype m k (class c) (class d)
with Md_Subtypes : PairNatList.t -> ct -> list md -> list md -> Prop :=
     | MDCons : forall md1 md2 mu k r mds,
         (In md1 mds) ->
         (Md_Subtype mu k md1 md2)-> (Md_Subtypes mu k mds r) -> 
         (Md_Subtypes mu k mds (md2::r))
     | MDNil : forall mu k mds, (Md_Subtypes mu k mds nil)
with Md_Subtype : PairNatList.t -> ct -> md -> md -> Prop :=
     | MDSub : forall mu k t1 t1' t2 t2' x x' e e' m, (Subtype mu k t1 t1') -> (Subtype mu k t2' t2) ->
                                                      Md_Subtype mu k (Method m x' t1' t2' e') (Method m x t1 t2 e).

Scheme subtyping_ind := Induction for Subtype Sort Prop
                        with md_subtypings_ind := Induction for Md_Subtypes Sort Prop
                                                  with md_subtype_ind := Induction for Md_Subtype Sort Prop.

Definition empty_mu := PairNatList.empty.

Hint Constructors Subtype.
Hint Constructors Md_Subtypes.

Inductive WellFormedType : ct -> type -> Prop :=
| WFWA : forall k, WellFormedType k Any
| WFWTC : forall k C fds mds, In (ClassDef C fds mds) k -> WellFormedType k (class C).

Inductive HasType : env -> heap -> ct -> expr -> type -> Prop :=
| KTSUB : forall g s k e t tp, HasType g s k e tp -> Subtype PairNatList.empty k tp t -> HasType g s k e t
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
    WellFormedType k t -> 
    HasType g s k e tp ->
    HasTypeExpr g s k (SubCast t e) t
| KTBEHCAST : forall g s k e t tp,
    WellFormedType k t -> 
    HasType g s k e tp ->
    HasTypeExpr g s k (BehCast t e) t
| KTREFTYPE : forall g s k a C t a',
    In (a,(HCell(C,a'))) s ->
    Subtype empty_mu k (class C) t ->
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

(*
Lemma mu_weakening : forall mu mu' k t1 t2,
  Subtype mu k t1 t2 -> Subtype (mu ++ mu') k t1 t2.
Proof. 
  intros. apply subtyping_ind with
          (P := fun mu => fun k => fun t1 => fun t2 => fun ih => Subtype (mu ++ mu') k t1 t2)
            (P0 := fun mu => fun k => fun mds1 => fun mds2 => fun ih => Md_Subtypes (mu ++ mu') k mds1 mds2)
            (P1 := fun mu k md1 md2 ih => Md_Subtype (mu ++ mu') k md1 md2); try eauto.
  - intros. apply STSeen. apply in_app_iff. eauto.
  - intros. eapply STClass.
    + intros.
      assert (Hin: In tp (m' ++ mu')).
      { apply in_or_app. apply in_app_or in H1. inject H1.
        - left. apply i. apply H2.
        - right. apply H2.
      }
      apply Hin.
    + apply in_or_app. left. eauto.
    + eauto.
  - intros. apply MDSub; eauto. 
Qed.
*)

Lemma subtype_transitive : forall mu k t1 t2 t3,
  Subtype mu k t1 t2 -> Subtype mu k t2 t3 -> Subtype mu k t1 t3. 
Admitted.

Lemma subtype_method_containment : forall k C D md,
    Subtype empty_mu k (class C) (class D) -> In md (methods D k) ->
    exists md', In md' (methods C k) /\ Md_Subtypes empty_mu k (md'::nil) (md::nil).
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
  HasType g s k e t -> exists tp, Subtype empty_mu k tp t /\ HasTypeExpr g s k e tp.
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
| NDUPTC : forall m x e mds t1 t2,
    NoDupsMds mds -> 
    (forall x' e' t1' t2', ~ In (Method m x' t1' t2' e') mds) ->
    NoDupsMds ((Method m x t1 t2 e)::mds)
| NDUPN : NoDupsMds nil.

Inductive NoDupsFds : list fd -> Prop :=
| NDUPFD : forall f t fds, NoDupsFds fds -> (forall t', ~ (In (Field f t') fds)) -> NoDupsFds ((Field f t)::fds)
| NDUPNI : NoDupsFds nil.

(*TODO: duplicate classes will need to change if we can extend the class table*)
(*TODO: NoDupsClasses will still be the same, right? Just need to ensure that it is not extended with a class
        that's already in the table.*)
Inductive NoDupsClasses : list k -> Prop :=
| NDUPK : forall C fds mds ks, NoDupsClasses ks -> (forall fds' mds', ~(In (ClassDef C fds' mds') ks)) ->
                               NoDupsClasses ((ClassDef C fds mds)::ks)
| NDUPNIL : NoDupsClasses nil.

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

Definition ct_ext (k : ct) (k' : ct) := exists k'',
           k' = k'' ++ k /\ NoDupsClasses k'.

(*CT extension basic property*)
Lemma ct_exten_refl : forall k,
    NoDupsClasses k -> ct_ext k k.
Proof.
  intros.
  unfold ct_ext.
  exists nil. simpl. repeat split; auto; try inject H0. 
Qed.

Hint Resolve ct_exten_refl. 

(*Lemmas for CT extensions*)

Lemma methods_implies_containment : forall m k C, In m (methods C k) ->
                                                  exists fds mds, In (ClassDef C fds mds) k.
Proof.
  intros. induction k0.
  - simpl in H. tauto.
  - simpl in H. destruct a. destruct (Nat.eqb C i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exists l. exists l0. apply in_eq.
    + apply IHk0 in H. inject H. inject H0.  exists x. exists x0. apply in_cons. apply H.
Qed.

Lemma fields_implies_containment : forall m k C, In m (fields C k) ->
                                                  exists fds mds, In (ClassDef C fds mds) k.
Proof.
  intros. induction k0.
  - simpl in H. tauto.
  - simpl in H. destruct a. destruct (Nat.eqb C i) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst. exists l. exists l0. apply in_eq.
    + apply IHk0 in H. inject H. inject H0.  exists x. exists x0. apply in_cons. apply H.
Qed.

Lemma ct_exten_methods : forall m k k' C, In m (methods C k) -> ct_ext k k' -> In m (methods C k').
Proof.
  intros. inject H0. inject H1. induction x.
  - simpl. apply H.
  - simpl. destruct a. simpl in H2. inject H2.  apply methods_implies_containment in H.
    inject H. inject H0. assert (Hin: (In (ClassDef C x0 x1) (x ++ k0))).
    { apply in_or_app. auto. }
    destruct (Nat.eqb C i) eqn:Heq.
    + rewrite Nat.eqb_eq in Heq. subst. apply H6 in Hin. tauto.
    + apply IHx. apply H3.
Qed.

Lemma ct_methods_eq : forall k k' C, WellFormedType k (class C) -> ct_ext k k' -> (methods C k) = (methods C k').
Proof.
  intros. inject H0. inject H1. induction x.
  - simpl. auto.
  - simpl. destruct a. destruct (Nat.eq_dec C i).
    + subst. inject H. inject H2. assert (Hin: In (ClassDef i fds mds) (x ++ k0)).
      { apply in_or_app. right. auto. }
      apply H6 in Hin. tauto.
    + rewrite<- Nat.eqb_neq in n. rewrite n. apply IHx. simpl in H2. inject H2. apply H3.
Qed.

Lemma ct_fields_eq : forall k k' C, WellFormedType k (class C) -> ct_ext k k' -> (fields C k) = (fields C k').
Proof.
  intros. inject H0. inject H1. induction x.
  - simpl. auto.
  - simpl. destruct a. destruct (Nat.eq_dec C i).
    + subst. inject H. inject H2. assert (Hin: In (ClassDef i fds mds) (x ++ k0)).
      { apply in_or_app. right. auto. }
      apply H6 in Hin. tauto.
    + rewrite<- Nat.eqb_neq in n. rewrite n. apply IHx. simpl in H2. inject H2. apply H3.
Qed.

Hint Resolve ct_fields_eq. 
Hint Resolve ct_exten_methods. 
Hint Resolve ct_methods_eq.
Hint Resolve fields_implies_containment.

Lemma fields_ct_ext : forall fd k k' C,
    ct_ext k k' -> In fd (fields C k) -> In fd (fields C k').
Proof.
  intros. pose proof H0. apply fields_implies_containment in H0. inject H0. inject H2.  
  erewrite<- ct_fields_eq; eauto. econstructor. apply H0. 
Qed.

Hint Resolve fields_ct_ext.

Lemma ct_exten_subtyp : forall m k t t' k',
        Subtype m k t t' -> ct_ext k k' -> Subtype m k' t t'.
Proof.
Admitted.

Hint Resolve ct_exten_subtyp.

Lemma ct_exten_wft : forall k k' t, WellFormedType k t -> ct_ext k k' -> WellFormedType k' t.
Proof.
  intros. inject H; try constructor. inject H0. inject H. econstructor. apply in_or_app.
  right. apply H1.
Qed.

Hint Resolve ct_exten_wft.
  
Lemma ct_exten_hastype : forall g s k e t k',
        HasType g s k e t -> ct_ext k k' -> HasType g s k' e t.
Proof.
  intros. pose proof (eq_refl k0). generalize dependent H1.
  pose proof (typing_ind (fun gi si ki ei ti ih => ki = k0 -> HasType gi si k' ei ti)
                         (fun gi si ki ei ti ih => ki = k0 -> HasTypeExpr gi si k' ei ti)
                         (fun gi si ki esi tsi ih => ki = k0 -> HasTypes gi si k' esi tsi)).
  apply H1; clear H1; try (intros; subst; econstructor; eauto; fail). 
  - intros. subst. econstructor; eauto. inject H0. inject H2.  apply in_or_app. right. apply i.
Qed.

(* Inductive expr :=
| Var : id -> expr
| Ref : ref -> expr (* location of object *)
| GetF : expr -> id -> expr
| SetF : expr -> id -> expr -> expr
| Call : expr -> id -> type -> type -> expr -> expr
| DynCall : expr -> id -> expr -> expr
| SubCast : type -> expr -> expr (* <t> *)
| BehCast : type -> expr -> expr (* << t >>*)
| New : id -> list expr -> expr. *)

Fixpoint WrapAny_methods(input_meth : md) (D_meth : list md) : md :=
  match input_meth with
  | Method m x t1 t2 e => Method m x Any Any (BehCast Any (Call (GetF (Var this) that) m t1 t2 (BehCast t1 (Var x))))
end.

Fixpoint Wrap_methods (input_meth : md) (D_meth : list md) : md :=
  match input_meth with
  | Method m x t1 t2 e => match method_def m D_meth with
                        | Some(Method m' x' t1' t2' e') => Method m x t1' t2' (BehCast t2' (Call (GetF (Var this) that) m t1 t2 (BehCast t1 (Var x))))
                        | None => Method m x t1 t2 (Call (GetF (Var this) that) m t1 t2 (Var x))
                        end
end.

Fixpoint Wrap_many_methods (mds1:list md) (mds2 : list md) :=
  match mds1 with
  | md::mdr => (Wrap_methods md mds2)::(Wrap_many_methods mdr mds2)
  | nil => nil
  end.

Fixpoint Wrap_many_any_methods (mds1 : list md) (mds2 : list md) :=
  match mds1 with
  | md::mdr => (WrapAny_methods md mds2)::(Wrap_many_any_methods mdr mds2)
  | nil => nil
  end.

Definition Wrap_classes (C : id) (md1 : list md) (md2 : list md) (D : id) : k :=
  ClassDef D ((Field that (class C))::nil) (Wrap_many_methods md1 md2).

Definition WrapAny_classes (C : id) (md1 : list md) (D : id) : k :=
  ClassDef D ((Field that (class C))::nil) (Wrap_many_any_methods md1 md1).

Lemma correctness_MWrapAny : forall m x t1 t2 e g s k md mds mds' C D,
    C <> D ->
    md = Method m x t1 t2 e ->
    In md (methods C ((ClassDef D ((Field that (class C))::nil) mds') :: k)) ->
    WellFormedMethod ((this, class C) :: g) s k md -> 
    WellFormedMethod ((this, class D) :: g) s ((ClassDef D ((Field that (class C))::nil) mds') :: k) (WrapAny_methods md mds).
Proof.
  intros.
  subst.
  simpl.
  constructor.
  - inject H2; eauto.
  - constructor.
    econstructor.
    constructor.
    constructor.
    econstructor.
    * simpl. constructor. econstructor.
      ** apply in_eq.
      ** simpl. rewrite -> Nat.eqb_refl.
         apply in_eq.
    * constructor. econstructor.
      ** inject H2.
        *** constructor.
        *** inject H11. econstructor. apply in_cons. eauto.
      ** constructor. econstructor. apply in_or_app. right. apply in_eq.
    * eauto.
Qed.


Lemma correctness_mdef : forall m x t1 t2 e mds,
    NoDupsMds mds ->
    Some (Method m x t1 t2 e) = (method_def m mds) <-> In (Method m x t1 t2 e) mds.
Proof.
  intros. split; intros.
  - induction mds.
    + simpl in H0. inversion H0.
    + simpl in H0. destruct a. destruct (Nat.eqb m i).
      * inject H0. apply in_eq.
      * apply in_cons. apply IHmds; eauto. inject H. eauto.
  - induction mds.
    + inject H0.
    + simpl. destruct a as [m' x' t1' t2' e']. inject H0.
      * inject H1. rewrite Nat.eqb_refl. auto.
      * destruct (Nat.eqb m m') eqn:Heq.
        ** apply Nat.eqb_eq in Heq. subst. inject H. apply H8 in H1. tauto.
        ** inject H. apply IHmds; eauto.
Qed.

Lemma mdef_same_name : forall i m mds x t1 t2 e, Some(Method i x t1 t2 e) = (method_def m mds) -> i = m.
Proof.
  intros. induction mds.
  - simpl in H. inject H.
  - simpl in H. destruct a. destruct (Nat.eqb m i0) eqn:Heq.
    + apply Nat.eqb_eq in Heq. inject H. auto.
    + apply IHmds in H. apply H.
Qed.

Definition fresh_class_name(C : id)(k : ct) :=
  forall fds mds, ~ In (ClassDef C fds mds) k.

Ltac ht :=
  match goal with
  | [ |- HasType _ _ _ _ _ ] => constructor
  | [ |- HasTypeExpr _ _ _ _ _ ] => econstructor
  end.

Hint Constructors HasType.
Hint Constructors HasTypeExpr.
Lemma correctness_MWrap : forall m x t1 t2 e g s k md mds mds' C D,
    WellFormedClassTable nil k -> fresh_class_name D k -> 
    C <> D -> NoDupsMds mds -> NoDupsMds mds' -> x <> this -> 
    md = Method m x t1 t2 e ->
    (forall md', In md' mds -> WellFormedMethod ((this, class C) :: g) s k md') ->
    In md (methods C k) ->
    WellFormedMethod ((this, class C) :: g) s k md -> 
    WellFormedMethod ((this, class D) :: g) s ((ClassDef D ((Field that (class C))::nil) mds') :: k)
                     (Wrap_methods md mds).
Proof.
  intros. subst. simpl.
  assert (Hctext: ct_ext k0 (ClassDef D (Field that (class C) :: nil) mds' :: k0)).
  { unfold ct_ext. exists ((ClassDef D (Field that (class C) :: nil) mds')::nil). split.
    - simpl. auto.
    - constructor.
      + inject H. auto.
      + unfold fresh_class_name in H0. apply H0. }
  assert (Hwt: forall t1 t2 t x' e',
             WellFormedType (ClassDef D (Field that (class C) :: nil) mds' :: k0) t1 ->
             In (Method m x t1 t2 e) (methods C k0) ->
             HasType (((this, class D) :: g) ++ (x', t) :: nil) s (ClassDef D (Field that (class C) :: nil) mds' :: k0) e' t1 ->
             HasTypeExpr (((this, class D) :: g) ++ (x', t) :: nil) s
                         (ClassDef D (Field that (class C) :: nil) mds' :: k0)
                         (Call (GetF (Var this) that) m t1
                               t2 e') 
                         t2).
  { intros. repeat (ht; eauto). 
    * simpl. left. auto.
    * simpl. rewrite Nat.eqb_refl. apply in_eq. }
  assert (Hwf: WellFormedType ((ClassDef D ((Field that (class C))::nil) mds') :: k0) t1 /\
               WellFormedType ((ClassDef D ((Field that (class C))::nil) mds') :: k0) t2).
  { inject H8; [split; try constructor|]. split; eauto. }
  inject Hwf. 
  destruct (method_def m mds) eqn:Hmd.
  - destruct m0 as [m' x' t1' t2' e']. symmetry in Hmd.
    pose proof (mdef_same_name m' m _ _ _ _ _ Hmd). subst.
    rewrite correctness_mdef in Hmd; eauto. apply H6 in Hmd. inject Hmd.
    + constructor; eauto. ht. ht; eauto; [constructor|]. ht. apply Hwt; eauto.
      repeat ht; eauto. apply in_or_app. right. apply in_eq. 
    + constructor; eauto.  ht. ht; [eauto|].
      ht. eapply Hwt; eauto. repeat ht; eauto. apply in_or_app. right. apply in_eq. 
  - inject H8.
    + constructor; eauto. ht. apply Hwt; eauto. repeat ht. apply in_or_app. right. apply in_eq.
    + constructor; eauto. ht. apply Hwt; eauto. repeat ht. apply in_or_app. right. apply in_eq. 
Qed.

Lemma correctness_WrapMany : forall md2 mds' mds'' md' C D k fds mds,
    fresh_class_name D k ->
    WellFormedClassTable nil k ->
    In (ClassDef C fds mds'') k ->
    NoDupsMds md2 -> NoDupsMds mds' ->
    (forall md' : md, In md' md2 -> WellFormedMethod ((this, class C) :: nil) nil k md') ->
    (forall md' : md, In md' mds -> WellFormedMethod ((this, class C) :: nil) nil k md') ->
    (forall md' : md, In md' mds -> In md' mds'') ->
    In md' (Wrap_many_methods mds md2) -> C <> D ->
    WellFormedMethod ((this, class D) :: nil) nil
                     ((ClassDef D ((Field that (class C))::nil) mds') :: k)
                     md'.
Proof.
  intros ? ? ? ? ? ? ? ? ? HFresh Hwfct HinC HNdmd2 HNdmd' Hforallmd2 Hforallmd Hsub HinMd Hneq.
  induction mds.
  - intros. simpl in HinMd. tauto.
  - intros. simpl in HinMd. inject HinMd; revgoals.
    + apply IHmds.
      * intros. apply Hforallmd. apply in_cons. auto.
      * intros. apply Hsub. apply in_cons. auto.
      * auto.
    + destruct a. specialize Hforallmd with (Method i i0 t t0 e).
      pose proof (Hforallmd (in_eq _ _)). inject H.
      * eapply correctness_MWrap; eauto.
        ** erewrite<- methods_in.
           *** apply Hsub. apply in_eq.
           *** apply Hwfct.
           *** apply HinC.
        ** apply Hforallmd. apply in_eq.
      * eapply correctness_MWrap; eauto.
        ** erewrite<- methods_in.
           *** apply Hsub. apply in_eq.
           *** apply Hwfct.
           *** apply HinC.
        ** apply Hforallmd. apply in_eq.
Qed.


Lemma correctness_WrapManyAny : forall md2 mds' mds'' md' C D s k fds mds,
    WellFormedClassTable s k ->
    In (ClassDef C fds mds'') k ->
    NoDupsMds md2 -> NoDupsMds mds' ->
    (forall md' : md, In md' md2 -> WellFormedMethod ((this, class C) :: nil) s k md') ->
    (forall md' : md, In md' mds -> WellFormedMethod ((this, class C) :: nil) s k md') ->
    (forall md' : md, In md' mds -> In md' mds'') ->
    In md' (Wrap_many_any_methods mds md2) -> C <> D ->
    WellFormedMethod ((this, class D) :: nil) s
                     ((ClassDef D ((Field that (class C))::nil) mds') :: k)
                     md'.
Proof.
  intros ? ? ? ? ? ? ? ? ? ? Hwfct HinC HNdmd2 HNdmd' Hforallmd2 Hforallmd Hsub HinMd Hneq.
  induction mds.
  - intros. simpl in HinMd. tauto.
  - intros. simpl in HinMd. inject HinMd; revgoals.
    + apply IHmds.
      * intros. apply Hforallmd. apply in_cons. auto.
      * intros. apply Hsub. apply in_cons. auto.
      * auto.
    + destruct a. specialize Hforallmd with (Method i i0 t t0 e).
      pose proof (Hforallmd (in_eq _ _)). inject H.
      * eapply correctness_MWrapAny.
        ** eauto.
        ** eauto.
        ** simpl. apply Nat.eqb_neq in Hneq. rewrite Hneq.
           erewrite<- methods_in.
           *** apply Hsub. apply in_eq.
           *** apply Hwfct.
           *** apply HinC.
        ** apply Hforallmd. apply in_eq.
      * eapply correctness_MWrapAny; eauto.
        ** simpl. apply Nat.eqb_neq in Hneq. rewrite Hneq.
           erewrite<- methods_in.
           *** apply Hsub. apply in_eq.
           *** apply Hwfct.
           *** apply HinC.
        ** apply Hforallmd. apply in_eq.
Qed.

Lemma MWrapManyAny_NoDups : forall mds mds', NoDupsMds mds -> NoDupsMds (Wrap_many_any_methods mds mds').
Proof.
  intros. induction mds.
  - simpl. constructor.
  - simpl. destruct a. simpl. constructor.
    + apply IHmds. inject H. auto.
    + intros. intros H0. clear IHmds. induction mds.
      * simpl in H0. tauto.
      * simpl in H0. inject H0.
        ** destruct a. simpl in H1. inject H1. inject H. specialize H7 with (x'0:=x')(e':=e0)(t1':= t1)(t2':=t2).
           apply H7. apply in_eq.
        ** apply IHmds.
           *** inject H. inject H3. constructor; eauto. intros. intro H. eapply H8. apply in_cons. apply H.
           *** auto.
Qed.
 
Lemma correctness_CWrapAny : forall k C D fds mds,
    In (ClassDef C fds mds) k -> C <> D -> WellFormedClassTable nil k ->
    NoDupsMds mds -> 
    WellFormedClass nil k (ClassDef C fds mds) -> 
    WellFormedClass nil (ClassDef D ((Field that (class C))::nil) (Wrap_many_any_methods mds mds) :: k)
                           (WrapAny_classes C mds D).
Proof.
  intros k0 C D fds mds Hin Hneq Hwfct Hndmd Hwfc. unfold WrapAny_classes. constructor.
  - intros. inject H; [|inject H0]. constructor. econstructor. apply in_cons. apply Hin.
  - intros. eapply correctness_WrapManyAny; eauto.
    + apply MWrapManyAny_NoDups; auto.
    + intros. inject Hwfc. apply H7; auto.
    + intros. inject Hwfc. apply H7; auto.
  - inject Hwfc. constructor; eauto. constructor.
  - apply MWrapManyAny_NoDups; auto.
Qed.

Lemma MWrapMany_NoDups : forall mds mds', NoDupsMds mds -> NoDupsMds (Wrap_many_methods mds mds').
Proof.
  intros. induction mds.
  - simpl. constructor.
  - simpl. destruct a. simpl. destruct (method_def i mds').
    + destruct m. constructor.
      * apply IHmds. inject H. apply H2.
      * intros. clear IHmds. induction mds.
        ** simpl. auto.
        ** simpl. intros H0. inject H0.
           *** destruct a. simpl in H1. destruct (method_def i1 mds').
               **** destruct m. inject H1. inject H. eapply H7. apply in_eq.
               **** inject H1. inject H. eapply H7. apply in_eq.
           *** apply IHmds in H1; auto. inject H. inject H3. constructor; eauto. intros. intros H. eapply H8.
               apply in_cons. apply H.
    + constructor.
      * apply IHmds. inject H. eauto.
      * intros. clear IHmds. induction mds.
        ** simpl. auto.
        ** simpl. intro H0. inject H0.
           *** destruct a. simpl in H1. destruct (method_def i1 mds').
               **** destruct m. inject H1. inject H. eapply H7. apply in_eq.
               **** inject H1. inject H. eapply H7. apply in_eq.
           *** eapply IHmds.
               **** inject H. inject H3. constructor; eauto. intros. intros H. eapply H8. apply in_cons. apply H.
               **** auto.
Qed.

Lemma correctness_CWrap : forall k C D fds mds mds',
    In (ClassDef C fds mds) k -> C <> D -> WellFormedClassTable nil k -> NoDupsMds mds' ->
    (forall md' : md, In md' mds' -> WellFormedMethod ((this, class C) :: nil) nil k md') ->
    WellFormedClass nil k (ClassDef C fds mds) -> fresh_class_name D k -> 
    WellFormedClass nil (ClassDef D ((Field that (class C))::nil) (Wrap_many_methods mds mds') :: k)
                    (Wrap_classes C mds mds' D).
Proof.
  intros ? ? ? ? ? ? Hin Hneq Hwfct Hndmd Hfamd' Hwfc Hfresh. constructor.
  - intros. inject H; [|inject H0]. repeat constructor. econstructor. apply in_cons. apply Hin.
  - intros. eapply correctness_WrapMany.
    * eauto.
    * eauto.
    * apply Hin.
    * apply Hndmd. 
    * apply MWrapMany_NoDups. inject Hwfc. auto.
    * intros. eauto.
    * inject Hwfc. apply H6.
    * intros. eauto.
    * auto.
    * apply Hneq.
  - constructor.
    + constructor.
    + intros t' H. inversion H.
  - apply MWrapMany_NoDups. inject Hwfc. apply H7.
Qed.

(*Lemmas for CT extensions ENDS*)


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

(*Lemmas for CT extensions*)
Lemma ct_exten_wfheap : forall s k k',
        WellFormedHeap k s /\ ct_ext k k' -> WellFormedHeap k' s.
Proof.
Abort.

(*Lemmas for CT extensions ENDS*)


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
| EBehCast : type -> EvalCtx -> EvalCtx
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
  | EBehCast t E => BehCast t (equivExpr ei E)
  | ENew C aps E ers => New C ((map Ref aps) ++ (equivExpr ei E)::ers)
  | EHole => ei
  end.

Fixpoint fresh_ref (s:heap)(i:nat) :=
  match s with
  | (a,hc)::r => match Nat.ltb a i with
                 | true => fresh_ref r i
                 | false => fresh_ref r (S a)
                 end
  | nil => i
  end.

Fixpoint fresh_class (k:ct)(i:nat) :=
  match k with
  | (ClassDef C fds mds)::r => match Nat.ltb C i with
                 | true => fresh_class r i
                 | false => fresh_class r (S C)
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

Import Syntax Coq.Lists.List.

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
    Subtype empty_mu k t1' t1 ->
    Subtype empty_mu k t2 t2' ->
    Steps k (Call (Ref a) m t1' t2' (Ref a')) s k (subst a a' x e) s
| SDynCall : forall a C aps s m x e k a',
    In (a, HCell(C,aps)) s ->
    In (Method m x Any Any e) (methods C k) ->
    Steps k (DynCall (Ref a) m (Ref a')) s k (subst a a' x e) s
| SDynCast : forall k a s, Steps k (SubCast Any (Ref a)) s k (Ref a) s
| SSubCast : forall a aps C D s k,
    In (a, HCell(C,aps)) s ->
    Subtype empty_mu k (class C) (class D) ->
    Steps k (SubCast (class D) (Ref a)) s k (Ref a) s
| SBehCastAny : forall a s (k:ct) ap C E (D:id) mds a' s' k' a'',
    In (a, HCell(C,ap)) s ->
    E = fresh_class k D ->
    C <> E ->
    a'' = fresh_ref s a' ->
    mds = (methods C k) ->
    NoDupsMds mds ->
    s' = (a'', HCell(E,  a::nil))::s ->
    k' = k ++ [(WrapAny_classes C mds E)] ->
    Steps k (BehCast (class E) (Ref a)) s k' (Ref a'') s'
| SBehCast : forall a s k ap C E D mds mds' C' a' s' k' a'',
    In (a, HCell(C,ap)) s ->
    E = fresh_class k D ->
    C <> E ->
    a'' = fresh_ref s a' ->
    mds = (methods C k) ->
    mds' = (methods C' k) ->
    incl mds mds' ->
    NoDupsMds mds' ->
    s' = (a'', HCell(E,  a::nil))::s ->
    k' = k ++ [(Wrap_classes C mds mds' E)] ->
    Steps k (BehCast (class E) (Ref a)) s k' (Ref a'') s'
| SCtx : forall k k' e s e' s' E,
    Steps k e s k' e' s' -> Steps k (equivExpr e E) s k' (equivExpr e' E) s'.
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

Theorem weakening_retains_refs: forall s s', retains_references s (s' ++ s).
Proof.
  intros. induction s.
  - unfold retains_references. intros. inversion H.
  - unfold retains_references. intros. inversion H.
    + exists aps. subst. apply in_or_app. right. apply in_eq.
    + exists aps. apply in_or_app. right. apply H.
Qed.


Lemma HasTypes_split : forall g s k e1 e2 fs1 fs2, 
  HasTypes g s k e1 fs1 ->
  HasTypes g s k e2 fs2 ->
  HasTypes g s k (e1 ++ e2) (fs1 ++ fs2).
Proof.
  intros. generalize dependent fs1. induction e1.
  - simpl. intros. inject H. rewrite app_nil_l. eauto.
  - simpl. intros. inject H. apply IHe1 in H8. eapply HTSCONS.
    + apply H6.
    + apply H8. 
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

Lemma typesof_cons : forall fds t1 ts, 
    typesof fds = t1::ts -> exists f fds', fds = (Field f t1)::fds'.
Proof.
  intros. generalize dependent ts. induction fds.
  - intros. inversion H.
  - intros. destruct a. exists i. exists fds. simpl in H. inject H. reflexivity.
Qed.

Lemma hastypes_split : forall s k e1s a1s t1s,
  FieldRefWellFormed k s t1s a1s -> 
  Deref e1s a1s ->
  HasTypes nil s k e1s t1s.
Proof.
  intros. generalize dependent a1s. generalize dependent t1s. induction e1s.
  - intros. inject H0. inject H. apply HTSNIL.
  - intros. inject H0. inject H. apply HTSCONS.
    + apply H6.
    + eapply IHe1s; eauto.
Qed.

Lemma hastypes_app : forall s k e1s e2s fd1s fd2s,
    HasTypes nil s k (e1s ++ e2s) (fd1s ++ fd2s) -> 
    HasTypes nil s k e1s fd1s ->
    HasTypes nil s k e2s fd2s.
Proof.
  intros. induction H0.
  - apply IHHasTypes. simpl in H. inversion H. subst. auto.
  - simpl in H. apply H.
Qed. 

Lemma fieldwf_still_good' : forall k fds aps s s', 
  FieldRefWellFormed k s fds aps ->
  retains_references s s' ->
  FieldRefWellFormed k s' fds aps.
Proof.
  intros. induction H.
  - apply FRWF_Cons; eauto. 
  - apply FRWF_Nil.
Qed.

Lemma cons_app_app_app : forall V x1 x y,
    x1 ++ x::y = @app V (x1 ++ (x::nil)) y.
Proof.
  intros. induction x1.
  - simpl. reflexivity.
  - simpl. rewrite IHx1. reflexivity.
Qed.

Lemma hastypes_ignores_heapv : forall g s k es fts s',
    HasTypes g s k es fts -> retains_references s s' -> HasTypes g s' k es fts.
Proof. 
  intros. induction H.
  - apply HTSCONS.
    + eauto.
    + apply IHHasTypes; eauto.
  - apply HTSNIL.
Qed.

Lemma app_cons_assoc: forall T a b c d,
    @cons T a b ++ @cons T c d = a::(b ++ c::d).
Proof.
  intros. simpl. reflexivity.
Qed.

Lemma frwf_deref_implies_eq_length : forall k s t1s a1s e1s,
    FieldRefWellFormed k s t1s a1s ->
    Deref e1s a1s -> length t1s = length e1s.
Proof.
  intros. generalize dependent a1s. generalize dependent t1s. 
  induction e1s. 
  - intros. inversion H0. simpl. inversion t1s.
    + intros. subst. inversion H. subst. reflexivity.
    + intros. subst. inversion H. subst. reflexivity.
  - intros. inversion H0. subst. inject H. simpl.
    assert (He:forall a b, a = b -> S a = S b).
    { intros. eauto. }
    apply He. eapply IHe1s; eauto.
Qed.


Lemma hastypes_shortening : forall s k a e1s e2s fds' t1s t' f,  
    HasTypes nil s k (e1s ++ a :: e2s) (t1s ++ Field f t' :: fds') ->
    length e1s = length t1s ->
    HasTypes nil s k (e1s ++ a :: nil) (t1s ++ Field f t' :: nil).
Proof.
  intros. generalize dependent t1s. induction e1s.
  - intros. inversion H0. destruct t1s.
    + simpl. simpl in H. inject H. eapply HTSCONS; eauto.
    + inversion H2.
  - intros. inversion H0. destruct t1s.
    + inversion H2. 
    + simpl. simpl in H. inject H. eapply HTSCONS; eauto.
Qed.

Lemma ht_any_expr : forall s k e, HasType nil s k e Any -> HasTypeExpr nil s k e Any.
Proof.
  intros. dependent induction H.
  - apply IHHasType.
    + eauto.
    + inversion H0; reflexivity.
  - apply H.
Qed.

Fixpoint succ_type_pairs (C:id) (k:ct) : list (id*id) :=
  match k with
    | (ClassDef D _ _)::r => (C,D) :: (D,C) :: (succ_type_pairs C r)
    | nil => nil
  end. 

Lemma stp_in : forall C D E k, In (C,D) (succ_type_pairs E k) ->
                                 (E = C \/ (D = E /\ exists fds mds, In (ClassDef C fds mds) k)) /\
                                 (E = D \/ (C = E /\ exists fds mds, In (ClassDef D fds mds) k)).
Proof.
  intros C D E k0 H0. induction k0.
  - simpl in H0. tauto.
  - simpl in H0. destruct a as [E' fds mds]. destruct H0.
    + inject H. split.
      *  left. auto.
      * right. split; auto. exists fds. exists mds. apply in_eq. 
    + inject H.
      * inject H0. split.
        ** right. split; auto. exists fds. exists mds. apply in_eq.
        ** left. auto.
      * apply IHk0 in H0. inject H0. destruct H; destruct H1.
        ** tauto.
        ** subst. split; [left;auto|]. right. destruct H0. destruct H0. destruct H0. split; auto. exists x. exists x0.
           apply in_cons; eauto.
        ** subst. split; [|left;auto]. right. destruct H. destruct H0. destruct H0. split; auto. exists x. exists x0.
           apply in_cons; eauto.
        ** destruct H as [Ceq [Cfds [Cmds HC]]]. destruct H0 as [Deq [Dfds [Dmds HD]]]. split; right. 
           *** split; auto. exists Cfds. exists Cmds. apply in_cons; eauto.
           *** split; auto. exists Dfds. exists Dmds. apply in_cons; eauto.    
Qed. 

Lemma stp_corr : forall C D k fds' mds',
    C <> D ->
    In (ClassDef D fds' mds') k ->
    In (C,D) (succ_type_pairs C k) /\ In (D,C) (succ_type_pairs C k).
Proof.
  intros. split.
  - induction k0.
    + inject H0.
    + simpl. destruct a as [E fds'' mds'']. destruct H0.
      * inject H0. apply in_eq.
      * apply in_cons. apply in_cons. apply IHk0. apply H0.
  - induction k0.
    + inject H0.
    + simpl. destruct a as [E fds'' mds'']. destruct H0.
      * inject H0. apply in_cons. apply in_eq. 
      * apply in_cons. apply in_cons. apply IHk0. apply H0.
Qed.

Lemma nodups_stp : forall C k,
    (forall fds mds, ~ In(ClassDef C fds mds) k) ->
    (NoDupsClasses k) ->
    NoDup (succ_type_pairs C k).
Proof.
  intros.  induction k0.
  - simpl. apply NoDup_nil.
  - simpl. destruct a as [D fds mds].
    apply NoDup_cons.
    + unfold not. intros. destruct H1.
      * inject H1. contradict H. unfold not. intros. 
        eapply H. apply in_eq.
      * apply stp_in in H1. destruct H1. destruct H2.
        ** subst. unfold not in H. eapply H. apply in_eq.
        ** inject H2. inject H4. inject H2. inversion H0. apply H9 in H4. tauto. 
    + apply NoDup_cons.
      * unfold not. intros. apply stp_in in H1. inject H1. destruct H2; destruct H3.
        ** subst. eapply H. apply in_eq.
        ** destruct H2. destruct H3. destruct H3. eapply H. apply in_cons. apply H3.
        ** inject H0. inject H1. inject H3. inject H0. apply H8 in H1. tauto.
        ** destruct H2 as [Ceq [Cfds [Cmds HC]]]. destruct H1 as [Deq [Dfds [Dmds HD]]].
            inject H0. eapply H6. apply HD. 
      * apply IHk0.
        ** intros. specialize H with (fds0:=fds0)(mds0:=mds0). apply not_in_cons in H.
           destruct H. apply H1.
        ** inject H0. apply H3.
Qed.

Fixpoint type_pair_universe (k:ct) : list (id*id) :=
  match k with
  | (ClassDef C _ _)::r => succ_type_pairs C r ++ type_pair_universe r
  | nil => nil
  end.

 
Lemma nodups_split : forall T a b, NoDup a -> NoDup b -> (forall x, In x a -> ~In x b) -> @NoDup T (a ++ b).
Proof.
  intros. induction H.
  - simpl. eauto.
  - simpl. apply NoDup_cons.
    + unfold not. intros. apply in_app_or in H3. destruct H3.
      * tauto.
      * specialize H1 with (x0:= x). apply H1 in H3; eauto. apply in_eq.
    + apply IHNoDup. intros. specialize H1 with (x0 := x0). apply H1. apply in_cons.
      apply H3.
Qed.

Lemma tpu_correct_1 : forall C D k, In (C, D) (type_pair_universe k) -> exists fds mds, In (ClassDef C fds mds) k.
Proof.
  intros. induction k0.
  - simpl in H. inject H.
  - destruct a as [E fds mds]. simpl in H. apply in_app_or in H. destruct H.
    + destruct (Nat.eq_dec C E).
      * subst. exists fds. exists mds. apply in_eq.
      * apply stp_in in H. destruct H. inject H.
        ** tauto.
        ** inject H1. inject H2. inject H. exists x. exists x0. apply in_cons. apply H1.
    + apply IHk0 in H. inject H. inject H0. exists x. exists x0. apply in_cons. eauto.
Qed.


Lemma tpu_correct_2 : forall C D k, In (C, D) (type_pair_universe k) -> exists fds mds, In (ClassDef D fds mds) k.
Proof.
  intros. induction k0.
  - simpl in H. inject H.
  - destruct a as [E fds mds]. simpl in H. apply in_app_or in H. destruct H.
    + destruct (Nat.eq_dec D E).
      * subst. exists fds. exists mds. apply in_eq.
      * apply stp_in in H. destruct H. inject H0.
        ** tauto.
        ** inject H1. inject H2. inject H0. exists x. exists x0. apply in_cons. apply H1.
    + apply IHk0 in H. inject H. inject H0. exists x. exists x0. apply in_cons. eauto.
Qed.

Lemma nodup_tpu : forall k, NoDupsClasses k -> NoDup (type_pair_universe k).
Proof.
  intros. induction k0.
  - simpl. apply NoDup_nil. 
  - simpl. destruct a as [C fds mds]. apply nodups_split.
    + apply nodups_stp.
      ** inject H. apply H5.
      ** inject H. apply H2.
    + apply IHk0. inject H. apply H2.
    + intros. destruct x as [C' D']. apply stp_in in H0. destruct H0. destruct H0; destruct H1.
      * subst. unfold not. intros. apply tpu_correct_1 in H0. inject H. inject H0. inject H. apply H6 in H0. tauto.
      * subst. unfold not. intros. apply tpu_correct_1 in H0. inject H. inject H0. inject H. apply H7 in H0. tauto.
      * subst. unfold not. intros. apply tpu_correct_2 in H1. inject H1. inject H2. inject H. apply H7 in H1. tauto.
      * unfold not. intros. destruct H0. destruct H1. subst. inject H. destruct H3 as [Hfds [Hmds H3]].
        apply H8 in H3. tauto.
Qed.

Fixpoint equivalent_set(x: list (id*id)) : PairNatList.t :=
  match x with
  | e :: r => PairNatList.add e (equivalent_set r)
  | nil => PairNatList.empty
  end.

Lemma equiv_set_corr : forall e x, In e x <-> PairNatList.In e (equivalent_set x).
Proof.
  intros. induction x.
  - simpl; split; try tauto. intros. inversion H. 
  - simpl. split.
    + destruct (PairNatList.E.eq_dec a e).
      * destruct a. destruct e. destruct r. inversion H. simpl in H1. subst. inversion H0. simpl in H1.
        subst. intros. apply PairNatList.add_spec. left. eauto.
      * intros. inject H.
        ** unfold not in n. contradict n. eauto.
        ** apply IHx in H0. apply PairNatList.add_spec. right. apply H0.
    + intros. apply PairNatList.add_spec in H. inject H.
      * destruct a. destruct e.  inversion H0. inversion H. inversion H1. simpl in *. subst. left. auto.
      * right. rewrite IHx. apply H0.
Qed.

Require Import Coq.MSets.MSetProperties.
Require Import Coq.MSets.MSetDecide.
Module MProps := WPropertiesOn(Nat_Pair_OT)(PairNatList).
Module MDec := Decide(PairNatList). 

Lemma add_diff_subset : forall e x y,
   PairNatList.Subset (PairNatList.diff x (PairNatList.add e y)) (PairNatList.diff x y).
Proof.
  intros. MDec.fsetdec. 
Qed.

Lemma tpu_correct : forall k C D, C <> D ->
                                  WellFormedType k (class C) -> WellFormedType k (class D) ->
                                  In (C,D) (type_pair_universe k).
Proof.
  intros. inject H0. inject H1. induction k0. 
  - inject H3. 
  - destruct a as [E fds' mds']. simpl. inject H3.
    + inject H0. inversion H4.
      * inject H0. tauto.
      * apply in_or_app. left. 
        assert (Hneq: D <> C). {
          contradict H0. auto.
        }
        pose proof (stp_corr D C k0 fds mds Hneq H0). inject H1. apply H3.
    + inject H4.
      * inject H1. apply in_or_app. left.
        pose proof (stp_corr C D k0 fds0 mds0 H H0). inject H1. apply H2.
      * apply in_or_app. right. apply IHk0; eauto.
Qed.

          
Lemma md_sub_lengthen : forall mu k md1 md2 md, Md_Subtypes mu k md1 md2 -> Md_Subtypes mu k (md::md1) md2.
  intros. induction H.
  - econstructor; eauto. apply in_cons. apply H.
  - constructor.
Qed.

Lemma wfm_implies_wft : forall ga s k m x t1 t2 e, WellFormedMethod ga s k (Method m x t1 t2 e) ->
                                                   (WellFormedType k t1) /\ (WellFormedType k t2).
Proof.
  intros. inject H.
  - split; try apply WFWA. 
  - repeat split; eauto.
Qed.

Lemma compute_md_subtype(k:ct)(m:PairNatList.t)(md1 md2 : md) ga ga'
      (wfmd1 : WellFormedMethod ga nil k md1)
      (wfmd2 : WellFormedMethod ga' nil k md2)
      (subtype : forall a b : type,
          WellFormedType k a -> WellFormedType k b ->
          {Subtype m k a b} + {~(Subtype m k a b)}) :
  {Md_Subtype m k md1 md2} + {~Md_Subtype m k md1 md2}.
Proof.
  destruct md1 as [mn ? t1' t2'], md2 as [mn' ? t1 t2].
  destruct (Nat.eq_dec mn mn'); revgoals. 
  - right. contradict n. inject n. auto.
  - apply wfm_implies_wft in wfmd1. apply wfm_implies_wft in wfmd2.
    inject wfmd1. inject wfmd2.
    pose proof (subtype t1 t1' H1 H). pose proof (subtype t2' t2 H0 H2).
    destruct H3; destruct H4.
    + left. constructor; eauto.
    + right. contradict n. inject n. apply H15.
    + right. contradict n. inject n. apply H7.
    + right. contradict n. inject n. apply H7.
Qed.

Lemma find_md_subtype(k:ct)(m:PairNatList.t)(md1 : md)(mds : list md) ga ga'
      s (wfmd1 : WellFormedMethod ga s k md1)(wfmd2 : forall md, In md mds -> WellFormedMethod ga' s k md)
      (subtype : forall a b : type, WellFormedType k a -> WellFormedType k b ->
          {Subtype m k a b} + {~(Subtype m k a b)}) :
  { exists md':md, In md' mds /\ Md_Subtype m k md' md1 } +
  {forall md', In md' mds -> ~Md_Subtype m k md' md1 }.
Proof.
  induction mds.
  - right. intros. inject H.
  - assert (Hih: forall md0 : md, In md0 mds -> WellFormedMethod ga' s k md0).
    { intros. pose proof (in_cons a md0 mds H). apply wfmd2 in H0. auto. }
    apply IHmds in Hih. clear IHmds. destruct Hih.
    + left. inject e. exists x. inject H. split; eauto. apply in_cons. apply H0.
    + destruct md1 as [mn ? t1' t2'], a as [mn' ? t1 t2]. apply wfm_implies_wft in wfmd1.
      specialize wfmd2 with (md0:=Method mn' i0 t1 t2 e0). pose proof (wfmd2 (in_eq _ _)).
      apply wfm_implies_wft in H. inject wfmd1. inject H. clear wfmd2.
      destruct (Nat.eq_dec mn mn'); destruct (subtype t1' t1 H0 H2); destruct (subtype t2 t2' H3 H1);
        try (right; intros; inject H; [contradict n0; inject n0; auto|apply n; apply H4]; fail).
      * subst. left. exists (Method mn' i0 t1 t2 e0). split.
        ** apply in_eq.
        ** constructor; eauto.           
Qed. 

Lemma compute_md_subtypes(k:ct)(m:PairNatList.t)(md1 md2 : list md) ga ga' 
      (s:heap)(wfmd1 : forall md, In md md1 -> WellFormedMethod ga s k md)
      (wfmd2 : forall md, In md md2 -> WellFormedMethod ga' s k md)
      (subtype : forall a b : type, WellFormedType k a -> WellFormedType k b ->
          {Subtype m k a b} + {~(Subtype m k a b)}) :
  {Md_Subtypes m k md1 md2} + {~(Md_Subtypes m k md1 md2)}.
  revert wfmd1. revert wfmd2. revert md1. induction md2.
  - left. constructor.
  - intros. specialize IHmd2 with (md1:=md1). destruct IHmd2; eauto.
    + intros.  apply wfmd2. apply in_cons. apply H.
    + destruct (find_md_subtype k m a md1 ga' ga s); eauto. 
      * apply wfmd2. apply in_eq.
      * left. inject e. inject H. econstructor; eauto.
      * right. intros H. inject H. apply n in H2. tauto.
    + right. contradict n. inject n. auto.
Qed.

Program Fixpoint compute_subtype (m : PairNatList.t)(s:heap)(k : ct)(kwf:WellFormedClassTable s k)
        (a b : type)(awf:WellFormedType k a)(bwf:WellFormedType k b)
        {measure (PairNatList.cardinal (PairNatList.diff (equivalent_set (type_pair_universe k)) m))}
  : {Subtype m k a b} + {~ (Subtype m k a b)} :=
  match a, b with
  | Any, Any => _
  | (class C), (class D) =>
    match (Nat.eqb C D) with
    | true => _
    | false =>
      match PairNatList.mem (C,D) m with
        true => _
      | false =>
        let mu' := PairNatList.add (C,D) m in
        let mc := (methods C k) in
        let mD := (methods D k) in
        _
      end
    end
  | Any, (class C) => _
  | (class C), Any => _
  end.
Next Obligation.
  left. eauto.
Qed.
Next Obligation.
  left. symmetry in Heq_anonymous. rewrite Nat.eqb_eq in Heq_anonymous. subst. auto.
Qed.
Next Obligation.
  left. symmetry in Heq_anonymous. apply MProps.Dec.F.mem_2 in Heq_anonymous. apply STSeen. eauto.
Qed.
Next Obligation.
  remember (methods C k0) as mc.
  remember (methods D k0) as mD.
  remember (PairNatList.add (C,D) m) as mu'.
  destruct (compute_md_subtypes k0 mu' mc mD ((this, (class C))::nil) ((this, (class D))::nil) s).
  - subst. apply methods_are_wf; eauto. 
  - subst. apply methods_are_wf; eauto.
  - refine (fun (a b:type)(wfa:WellFormedType k0 a)(wfb:WellFormedType k0 b) =>
              compute_subtype mu' s k0 kwf a b wfa wfb _).
    eapply MProps.subset_cardinal_lt.
    + MDec.fsetdec.
    + assert (Hin: PairNatList.In (C,D) (PairNatList.diff (equivalent_set (type_pair_universe k0)) m)).
      {
        subst. apply MProps.FM.diff_3.
        - rewrite<- equiv_set_corr. apply tpu_correct; eauto. symmetry in Heq_anonymous0.
          rewrite Nat.eqb_neq in Heq_anonymous0. eauto.
        - symmetry in Heq_anonymous. rewrite<- MProps.Dec.F.not_mem_iff in Heq_anonymous. eauto. 
      } apply Hin.
    + rewrite PairNatList.diff_spec. unfold not. intros. inject H. apply H1.
      rewrite PairNatList.add_spec. left. auto.
  - left. subst. eapply STClass; eauto.
  - right. contradict n. inject n.
    + symmetry in Heq_anonymous0. rewrite Nat.eqb_neq in Heq_anonymous0. tauto.
    + symmetry in Heq_anonymous. rewrite<- MProps.Dec.F.not_mem_iff in Heq_anonymous. tauto.
    + apply H4.
Qed.
Next Obligation.
  right. intros H. inject H.
Qed.
Next Obligation.
  right. intros H. inject H.
Qed.

Lemma ref_has_cell' : forall g s k a t, HasTypeExpr g s k (Ref a) t -> exists hc, In (a, hc) s.
Proof.
  intros. inject H.  
  - exists (HCell(C,a')). auto. 
  - exists hc. auto. 
Qed.

Lemma ref_has_cell : forall g s k a t, HasType g s k (Ref a) t -> exists hc, In (a, hc) s.
Proof.
  intros. apply eventually_concrete in H. inject H. inject H0. eapply ref_has_cell'; eauto.
Qed.


Lemma forall_same_size : forall T T' a b P, @Forall2 T T' P a b -> length a = length b.
Proof.
  intros. induction H.
  - auto.
  - simpl. auto.
Qed.
Lemma hastypes_same_length : forall s k a b, HasTypes nil s k a b -> length a = length b.
Proof.
  intros. induction H.
  - simpl. omega.
  - simpl. auto.
Qed.
Lemma same_size_prefix_hts : forall s k a b a' b' P,
    HasTypes nil s k (a ++ b) (a' ++ b') ->
    Forall2 P b b' ->
    length a = length a'.
Proof.
  intros. induction H0.
  - repeat rewrite app_nil_r in H. induction H.
    + simpl. omega.
    + auto.
  - apply hastypes_same_length in H. repeat rewrite app_length in H.
    apply forall_same_size in H1. simpl in H. rewrite H1 in H. omega.
Qed.


Ltac unfolde name :=
  match goal with
  | [ H : (exists a:?t, _) |- (exists b:?t, _) ] => let v' := a in
                                                    destruct H as [name H];
                                                    exists name end.

Lemma ref_is_finished : forall k e s k' e' s' a, Steps k e s k' e' s' -> e <> Ref a.
Proof.
  intros. contradict H. intros H'. subst. dependent induction H'.
  - destruct E;
      try (match goal with [ H: (equivExpr ?E ?c) = Ref ?a |- _] => simpl in H; inversion H; fail end).
    simpl in x. apply IHH' in x. tauto.
Qed.

Lemma ct_exten_refl'' : forall s k,
    WellFormedClassTable s k -> ct_ext k k.
Proof.
  intros. inject H. eauto.
Qed.
Hint Resolve ct_exten_refl''. 

Lemma frwf_exten_ctx : forall k k' s fs1 a1s, 
    FieldRefWellFormed k s fs1 a1s -> ct_ext k k' -> FieldRefWellFormed k' s fs1 a1s.
Proof.
  intros. induction H.
  - econstructor.
    + eapply ct_exten_hastype; eauto.
    + apply IHFieldRefWellFormed. eauto.
  - constructor.
Qed.

Lemma ct_exten_hastypes :forall (g : env) (s : heap) (k : ct) e t (k' : ct),
    HasTypes g s k e t -> ct_ext k k' -> HasTypes g s k' e t.
Proof.
  intros. induction H.
  - econstructor.
    + eapply ct_exten_hastype; eauto.
    + eauto.
  - eauto.
Qed. 

Hint Resolve frwf_exten_ctx.
Hint Resolve ct_exten_hastypes.
Ltac eval_ctx E :=
  match goal with
  | [ H: Steps _ ?e1 _ ?k ?e2 ?s |- _ ] =>
    exists (equivExpr e2 E); exists s; exists k;
    match goal with
    | [ H' : (WellFormedState _ _ ?s') |- context[(Steps _ ?e3 _ _ ?e4 ?s')]] =>
      let Htype := fresh "H" in
      let Hleft := fresh "H" in
      match goal with
      | [|- context[(HasType nil s' ?k e4 ?t)]] => assert (Htype:HasType nil s' k e4 t)
      end;
      [|assert (Hleft: e3 = (equivExpr e1 E));
        [try (subst; eauto;fail)| rewrite Hleft; clear Hleft; repeat split;
                                  [eauto| subst; simpl; try (inject H'; eapply WFSWP;eauto)
                                   | apply Htype | eauto | eauto ]]]
    end
  end.

  
Definition is_sound(k:ct)(s:heap)(e:expr)(t:type) :=
  (exists a : ref, e = Ref a) \/
  (exists (e' : expr) (s' : heap)(k':ct), Steps k e s k' e' s' /\
                                           WellFormedState k' e' s' /\
                                           HasType nil s' k' e' t /\
                                           retains_references s s' /\
                                           ct_ext k k') \/
  (exists E : EvalCtx,
      (exists (a : ref) (m : id) (a' : ref) (C : id) (aps : list ref),
          (e = equivExpr (DynCall (Ref a) m (Ref a')) E) /\
          In (a, HCell(C, aps)) s /\
          forall x e, ~ (In (Method m x Any Any e) (methods C k))) \/
      (exists (t' : type) (a : ref) (C : id) (aps:list ref),
          (e = equivExpr (SubCast t' (Ref a)) E) /\
          In (a, HCell(C,aps)) s /\
          ((Subtype empty_mu k (class C) t') -> False)) \/
      (exists t0 a, e = equivExpr (BehCast t0 (Ref a)) E)).


Lemma sound_destr : forall k s e2s t2s,
    Forall2 (is_sound k s) e2s (typesof t2s) ->
    Forall2 (fun e fd => match fd with (Field f t) => is_sound k s e t end) e2s t2s.
Proof.
  intros. dependent induction H.
  - destruct t2s.
    + constructor.
    + simpl in x. destruct f. inject x.
  - destruct t2s.
    + inject x.
    + constructor.
      * destruct f. simpl in x. inject x. auto.
      * apply IHForall2. simpl in x. destruct f. inject x. auto.
Qed.

Hint Resolve ct_exten_refl. 

Ltac sync_destruct_exists H :=
  repeat (let x := fresh "x" in destruct H as [x H]; exists x).

Ltac got_stuck E :=
  match goal with
  | [ H : ?H1 \/ ?H2 \/ ?H3 |- exists Ei : EvalCtx, _ \/ _ \/ _ ] =>
    exists E;
    destruct H; [|destruct H]; [left |
                                right; left |
                                right; right]; sync_destruct_exists H;
    try (destruct H; subst; eauto; fail);
    try (subst; simpl; auto; fail)
  end.

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
             (forall ei eir, ei::eir = e2s -> forall a, ei <> Ref a) /\
             @Forall2 expr type (is_sound k s) e2s (typesof t2s));
    try (intros; subst; inversion i; fail); try (intros; subst; unfold is_sound; eauto; fail). 
  - intros. subst. destruct H; eauto.
    + unfold is_sound. eauto.
    + unfold is_sound. right. destruct H.
      * left. unfolde e'. unfolde s'. unfolde k'.
        destruct H  as [H1 [H2 [H3 [H4 H5]]]].
        repeat split; eauto. 
      * right. eauto.
  - intros. subst. destruct H; try (unfold is_sound); eauto.
  - intros. subst. unfold is_sound. right. left.
    destruct (infields_implies_fieldin _ _ _ _ _ _ _ Hwfh Hwfct i i0) as [a'' H1].
    exists (Ref a''). exists s. exists k. repeat split; eauto.
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
      exists k. 
      assert (HHwrite: HeapWrite a aps' s s').
      { rewrite Heqs'. eapply update_heap_writes; eauto. }
      assert (HFwrite: FieldWrite f x a' fds aps').
      { eapply update_field_is_well_formed; eauto. destruct Hwfh. apply a0 in i.
        inject i. apply H0. }
      repeat split; try eauto.
      ** subst. eapply SWrite; eauto.
      ** eapply WFSWP; eauto.
         *** eapply write_field; eauto. 
             **** rewrite Heqfds in i0. apply i0. 
             **** subst. apply HFwrite.
         *** eapply wfct_doesnt_care; eauto. eapply heapwrite_retains_refs'; eauto.
      ** eapply heapwrite_retains_refs'; eauto.
    * unfold is_sound. right. inject H.
      ** left. destruct H0 as [e' [s' [k' [HS [Hwfs [Hht' [Hret Hct]]]]]]]. 
         eval_ctx (EAssign a f (EHole)). simpl. constructor. apply Hret in i. inject i. eauto. 
      ** right. destruct H0. got_stuck (EAssign a f x).
  - intros. subst. destruct H;eauto; destruct H0;eauto. 
    + destruct H as [a1 H1]. destruct H0 as [a2 H2]. subst. apply eventually_concrete in h.
      unfold is_sound. right. left.
      destruct h as [tp [H1 H2]]. inversion H2; eauto.
      * subst. pose proof (subtype_transitive _ _ _ _ _ H6 H1).
        apply subtype_method_containment with (md0 := (Method m x t0 t' eb)) in H; eauto.
        inversion H as [[m' x' t0' t'' e'] [H3 H4]]. inversion H4. subst. inject H8; [|inversion H5].
        remember (subst a1 a2 x' e') as ebody. exists ebody. exists s. exists k. 
        assert (Hbody: HasType nil s k ebody t').
        {
          inject H12. 
          pose proof H0 as Hback. inversion Hwfh. subst. apply H7 in H0. destruct H0.
          pose proof H0. inversion H0. subst. remember (methods C0 k) as mds'.
          pose proof (methods_are_wf s k C0 mds' Hwfct H9 Heqmds'). subst. apply H11 in H3.
          inversion H3.
          **** subst. simpl in H24. eapply substituion_typing; eauto.
          **** subst. simpl in H26. eapply substituion_typing; eauto. 
        }
        repeat split; eauto.
        *** inject H12. eapply SCall with (C:=C0)(aps := a'); eauto.
      * subst. inversion H1.
    + destruct H as [a H]. subst. destruct H0.
      * unfold is_sound. right. left. inversion H as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]].
        eval_ctx (ECall2 a m t0 t' EHole). simpl. constructor. econstructor.
        ** eapply ct_exten_hastype; eauto.
        ** eauto.
        ** eauto. 
      * unfold is_sound. right. right. destruct H as [E H].
        got_stuck (ECall2 a m t0 t' E). 
    + destruct H.
      * inversion H as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]]. unfold is_sound.
        right. left.
        eval_ctx (ECall1 EHole m t0 t' e'). constructor. econstructor; eauto. eapply ct_exten_hastype; eauto. 
      * destruct H as [E H]. unfold is_sound. right. right.
        got_stuck (ECall1 E m t0 t' e').
    + destruct H as [Hlef | Hrigh].
      * unfold is_sound. right. left. inversion Hlef as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]].
        eval_ctx (ECall1 (EHole) m t0 t' e'). simpl. constructor. econstructor; eauto.
        eapply ct_exten_hastype; eauto.
      * right. right. inject Hrigh. got_stuck (ECall1 x0 m t0 t' e').
  - intros. subst. destruct H; destruct H0; eauto.
    + unfold is_sound. right. destruct H as [a H]; subst. destruct H0 as [a' H0]; subst.
      apply ht_any_expr in h0. apply ht_any_expr in h. inject h.
      * inject H4.  
      * destruct hc. destruct p as [C a'0]. edestruct (fun dec => in_dec dec (m, Any, Any)
                          (map (fun md => match md with Method m _ t1 t2 _ => (m,t1,t2) end) (methods C k))).
        ** decide equality; eauto using type_dec. decide equality; eauto using type_dec, Nat.eq_dec.
        ** apply in_map_iff in i. destruct i as [md H]. destruct md. destruct H. inject H.
           left. exists (subst a a' i0 e0). exists s. exists k. 
           assert (Hmtyped : HasType nil s k (subst a a' i0 e0) Any).
           {
               inject Hwfh. pose proof H3. apply H1 in H3. destruct H3.
               pose proof (methods_are_wf s k C (methods C k) Hwfct H3 eq_refl (Method m i0 Any Any e0) H0).
               inject H5. eapply substituion_typing; eauto.
               **** apply H13.
           }           
           repeat split; eauto.  
        ** right. exists EHole. left. simpl. exists a. exists m. exists a'. exists C. exists a'0.
           repeat split; eauto.
           *** intros. contradict n. apply in_map_iff. exists (Method m x Any Any e0). split; eauto.
    + destruct H0.
      * inversion H0 as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]]. unfold is_sound.
        right. left. inversion H as [a]. subst.
        eval_ctx (EDCall2 a m EHole). simpl. constructor. econstructor; eauto. eapply ct_exten_hastype; eauto. 
      * destruct H as [a H]. subst. destruct H0 as [E H0]. 
        unfold is_sound. right. right. remember (EDCall2 a m E) as E'. exists E'. destruct H0.
        ** left. sync_destruct_exists H. intuition idtac. subst. eauto.
        ** destruct H.
           *** right. left. sync_destruct_exists H. inject H. subst. simpl. auto.
           *** right. right. sync_destruct_exists H. subst. simpl. auto. 
    + destruct H0 as [a H0]. subst. destruct H.
      * unfold is_sound. right. left. remember (EDCall1 EHole m (Ref a)) as E.
        inversion H as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]].
        assert (Hleft: equivExpr e0 E = (DynCall e0 m (Ref a))).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = DynCall e0' m (Ref a)).
        { subst. tauto. }
        assert (Htyped: HasType nil s' k' (equivExpr e0' E) Any).
        { rewrite Hright. apply KTEXPR. eapply KTDYNCALL; eauto. eapply ct_exten_hastype; eauto. }
        exists (equivExpr e0' E). exists s'. exists k'. repeat split; eauto.
        ** rewrite <- Hleft. eapply SCtx; eauto.
        ** inject H2. eapply WFSWP; eauto.
      * unfold is_sound. right. right. destruct H as [E H]. remember (EDCall1 E m (Ref a)) as E'.
        exists E'. inversion H.
        ** left. sync_destruct_exists H0. destruct H0. subst. eauto. 
        ** right. destruct H0.
           *** left. inversion H0 as [t'' [a' [C' [aps [He [H1 H2]]]]]]. exists t''.
               exists a'. exists C'. exists aps. subst. auto.
           *** right. sync_destruct_exists H0. subst. auto. 
    + clear H0. destruct H.
      * unfold is_sound. right. left. remember (EDCall1 EHole m e') as E.
        inversion H as [e0' [s' [k' [H1 [H2 [H3 [H4 H5]]]]]]].
        assert (Hleft: equivExpr e0 E = (DynCall e0 m e')).
        { subst. tauto. }
        assert (Hright: equivExpr e0' E = DynCall e0' m e').
        { subst. tauto. }
        assert (Htyped: HasType nil s' k' (equivExpr e0' E) Any).
        { rewrite Hright. apply KTEXPR. eapply KTDYNCALL; eauto. eapply ct_exten_hastype; eauto. }
        exists (equivExpr e0' E). exists s'. exists k'. repeat split; eauto.
        ** rewrite <- Hleft. eapply SCtx; eauto.
        ** inject H2. eapply WFSWP; eauto.
      * unfold is_sound. right. right. destruct H as [E H]. remember (EDCall1 E m e') as E'.
        exists E'. inversion H.
        ** left. sync_destruct_exists H0. destruct H0. subst. eauto. 
        ** right. destruct H0.
           *** left. inversion H0 as [t'' [a' [C' [aps [He [H1 H2]]]]]].
               exists t''. exists a'. exists C'. exists aps. subst. simpl. auto.
           *** right. sync_destruct_exists H0. subst. simpl. auto. 
  - intros. subst. destruct H as [e1s H]; eauto. destruct H as [a1s [t1s [e2s [t2s [H [H0 [H1 H2]]]]]]]. 
    induction e2s.
    + rewrite app_nil_r in H. subst. inversion H2. destruct t2s; eauto.
      * clear H2. unfold is_sound. right. left.
        remember (fresh_ref s 0) as a.
        remember (HCell(C,a1s)) as hc.
        remember ((a,hc)::s) as s'.
        exists (Ref a). exists s'. exists k. repeat split; eauto. 
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
        ** reflexivity.
        ** eauto.
      * destruct H. 
        ** left. destruct H as [e' [s' [k' [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]]]].
           eval_ctx (ENew C a1s EHole e2s); revgoals.
           { subst. simpl. rewrite deref_map with (e1s:=e1s)(a1s:=a1s); eauto. }
           { subst. simpl. rewrite<- deref_map with (e1s:=e1s)(a1s:=a1s); eauto.
             symmetry in H9. pose proof (typesof_cons t2s t' tps H9).
             destruct H as [f [fds' Heq]]. 
             eapply KTEXPR. eapply KTNEW; eauto.
             - apply HasTypes_split.
               + eapply hastypes_split; eauto. 
                 * eapply fieldwf_still_good'; eauto.
               + rewrite Heq. eapply HTSCONS; eauto. 
                 * eapply hastypes_app.
                   ** rewrite Heq in h. rewrite cons_app_app_app in h.
                      pose proof (cons_app_app_app fd t1s). rewrite H in h.
                      eapply hastypes_ignores_heapv; eauto. 
                   ** rewrite Heq in h. eapply hastypes_shortening.
                      *** eapply hastypes_ignores_heapv; eauto.
                      *** symmetry. eapply frwf_deref_implies_eq_length; eauto.
             - rewrite <- Heq. inject Hi5. inject H. apply in_or_app. right. eauto. }
        ** right. inversion H as [E]. exists (ENew C a1s E e2s). destruct H0.
           *** left. sync_destruct_exists H0. destruct H0. simpl. rewrite<- H0.
               apply deref_map in H2. rewrite <- H2. destruct H7. repeat split; eauto. 
           *** right. sync_destruct_exists H0. destruct H0. subst. destruct H7.
               simpl. rewrite (deref_map _ _ H2). repeat split; eauto.
  - intros. subst. destruct H; try tauto.
    + destruct H as [a H]. subst. unfold is_sound. pose proof h as h'.
      apply eventually_concrete in h. inject h. inject H. apply ref_has_cell' in H1. 
      pose proof Hwfh as Hwfh'. inject Hwfh. pose proof H2. inject H1. destruct x0. destruct p as [C a'].
      pose proof H4 as HIn. apply H2 in H4. inject H4.
      destruct (compute_subtype empty_mu s k Hwfct (class C) t0 H1 w).
      ** right. left. exists (Ref a). exists s. exists k. repeat split; eauto.
         *** pose proof s0. apply subtype_only_classes in s0. inject s0. eapply SSubCast; eauto. 
         *** eapply WFSWP; eauto. econstructor; eauto.
      ** right. right. exists EHole. right. exists t0. exists a. exists C. exists a'. repeat split; eauto.
    + destruct H.
      * destruct H as [e' [s' [k' [HSteps [HWFS [HHT [Hrr Hext]]]]]]]. unfold is_sound. right. left.
        eval_ctx (ESubCast t0 EHole). simpl. eauto. 
      * inject H. unfold is_sound. right. right. exists (ESubCast t0 x). inject H0.
        ** left. sync_destruct_exists H. inject H. inject H1. repeat split; eauto.
        ** right. sync_destruct_exists H. inject H. inject H1. repeat split; eauto.
  - intros. subst. destruct H; eauto; revgoals.
    + right. inject H.
      * left. destruct H0 as [e' [s' [k' [Hi1 [Hi2 [Hi3 [Hi4 Hi5]]]]]]].
        eval_ctx (EBehCast t0 EHole). simpl. eauto.
      * right. destruct H0 as [E [H1| H2]]; exists (EBehCast t0 E). 
        ** left. sync_destruct_exists H1. inject H1. split; auto.
        ** right. sync_destruct_exists H2. inject H2. split; auto.
    + destruct H as [a H]. subst. unfold is_sound. 
  - intros. pose proof (H0 H1 H2 H3).  pose proof (H H1 H2 H3) as H'.
    destruct H4 as [e1s [a1s [t1s [e2s [t2s H4]]]]].
    inject H4. inject H6. inject H2. inject H3. inject H4. clear H0.
    inject H'.
    + inject H0. exists ((Ref x) :: e1s). exists (x::a1s). exists (Field f t0 :: t1s). 
      exists e2s. exists t2s. repeat split; eauto; constructor; eauto. 
    + exists nil. exists nil. exists nil. exists (e0 :: e1s ++ e2s). exists (Field f t0 :: t1s ++ t2s). simpl.
      repeat split; eauto; try constructor. 
      * intros. inject H4. inject H0.
        ** destruct H4 as [? [? [? [? [H6]]]]]. eapply ref_is_finished. apply H0.
        ** inject H4. inject H0.
           *** destruct H4 as [? [? [? [? [? [Heq H6]]]]]]. subst. unfold not. intros.
               destruct x; try (simpl in H0; inject H0).
           *** destruct H4 as [? [? [? [? [Heq H4]]]]]. subst. unfold not. intros.
               destruct x; try (simpl in H0; inject H0).
      * right. apply H0.
      * generalize dependent t1s. generalize dependent a1s. induction e1s.
        ** intros. simpl. pose proof H5. apply sound_destr in H5. apply (same_size_prefix_hts _ _ _ _ _ _ _ h0) in H5.
           destruct t1s. 
           *** simpl. apply H4.
           *** simpl in H5. inject H5.
        ** intros. destruct t1s.
           *** apply sound_destr in H5. apply (same_size_prefix_hts _ _ _ _ _ _ _ h0) in H5. simpl in H5.
               inject H5.
           *** simpl. destruct f0. pose proof H2 as H2'. inject H2. constructor.
               **** left. exists a0. auto.
               **** eapply IHe1s; eauto.
                    ***** inject h0. auto.
                    ***** inject H1. auto. 
  - intros. subst. exists nil. exists nil. exists nil. exists nil. exists nil. repeat split; eauto; try econstructor.
    intros. inject H.
Admitted.