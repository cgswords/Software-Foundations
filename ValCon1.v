Require Import SfLib.

Module ValCon.

(* Types *)
Inductive ty : Type :=
  | TBool  : ty
  | TInt   : ty
  | TUnit : ty
  | TArrow : ty -> ty -> ty
  | TChan  : ty -> ty
  | TPair  : ty -> ty -> ty
  | TSum   : ty -> ty -> ty.

(* Terms *)

Inductive tm : Type :=
  | tvar   : id -> tm
  | ttrue  : tm
  | tfalse : tm
  | tnum   : nat -> tm
  | tunit  : tm
  | tchan  : nat -> tm
  | tapp   : tm -> tm -> tm
  | tabs   : id -> ty -> tm -> tm
  | tif    : tm -> tm -> tm -> tm
  | tpair  : tm -> tm -> tm
  | tfst   : tm -> tm
  | tsnd   : tm -> tm
  | tleft  : tm -> tm
  | tright : tm -> tm
  | tcase  : tm -> id -> tm -> id -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"
  | Case_aux c "ttrue"
  | Case_aux c "tfalse"
  | Case_aux c "tnum"
  | Case_aux c "tunit"
  | Case_aux c "tchan"
  | Case_aux c "tapp"
  | Case_aux c "tabs"
  | Case_aux c "tif"
  | Case_aux c "tpair"
  | Case_aux c "tfst"
  | Case_aux c "tsnd"
  | Case_aux c "tleft"
  | Case_aux c "tright"
  | Case_aux c "tcase"
  ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Inductive value : tm -> Prop :=
  | v_true : value ttrue
  | v_false : value tfalse
  | v_num   : forall n, value (tnum n)
  | v_unit  : value tunit
  | v_chan  : forall n, value (tchan n)
  | v_pair  : forall v1 v2, value v1 -> value v2 -> value (tpair v1 v2)
  | v_left  : forall v, value v -> value (tleft v)
  | v_right : forall v, value v -> value (tright v)
  | v_abs   : forall x T t, value (tabs x T t).

Hint Constructors value.

Reserved Notation "'[' x ':=' s ']' t" (at level 20).

Fixpoint subst (x:id) (s:tm) (t:tm) : tm :=
  match t with
  | tvar x' =>
      if eq_id_dec x x' then s else t
  | ttrue =>
     ttrue
  | tfalse =>
     tfalse
  | tnum n =>
     tnum n
  | tunit =>
     tunit
  | tchan n =>
     tchan n
  | tabs x' T t1 =>
      tabs x' T (if eq_id_dec x x' then t1 else ([x:=s] t1))
  | tapp t1 t2 =>
      tapp ([x:=s] t1) ([x:=s] t2)  
  | tif t1 t2 t3 =>
    tif ([x:=s] t1) ([x:=s] t2) ([x:=s] t3)
  | tpair t1 t2 =>
     tpair ([x:=s] t1) ([x:=s] t2)
  | tfst t1 =>
    tfst ([x:=s] t1)
  | tsnd t1 =>
    tsnd ([x:=s] t1)
  | tleft t1 =>
    tleft ([x:=s] t1)
  | tright t1 =>
    tright ([x:=s] t1)
  | tcase t0 x1 t1 x2 t2 =>
    tcase ([x:=s] t0)
          x1 (if eq_id_dec x x1 then t1 else ([x:=s] t1))
          x2 (if eq_id_dec x x2 then t2 else ([x:=s] t2))
  end

where "'[' x ':=' s ']' t" := (subst x s t).

(* Assuming subst on closed terms. *)

Reserved Notation "t1 '==>' t2" (at level 40).

Inductive step : tm -> tm -> Prop :=
| St_AppAbs : forall x T t12 v2,
    value v2 ->
   (tapp (tabs x T t12) v2) ==> [x:=v2]t12
| St_AppL : forall t1 t1' t2,
    t1 ==> t1' ->
    tapp t1 t2 ==> tapp t1' t2
| St_AppR : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    tapp v1 t2 ==> tapp v1 t2'
| St_IfTrue : forall t1 t2,
    (tif ttrue t1 t2) ==> t1
| St_IfFalse : forall t1 t2,
    (tif tfalse t1 t2) ==> t2
| St_If : forall t1 t2 t0 t0',
    t0 ==> t0' ->
    tif t0 t1 t2 ==> tif t0' t1 t2
| St_PairL : forall t1 t1' t2,
    t1 ==> t1' ->
    tpair t1 t2 ==> tpair t1' t2
| St_PairR : forall v1 t2 t2',
    value v1 ->
    t2 ==> t2' ->
    tpair v1 t2 ==> tpair v1 t2'
| St_Fst : forall t1 t1',
    t1 ==> t1' ->
    tfst t1 ==> tfst t1'
| St_Fst_V : forall v1 v2,
    value v1 ->
    value v2 -> 
    (tfst (tpair v1 v2)) ==> v1
| St_Snd : forall t1 t1',
    t1 ==> t1' ->
    tsnd t1 ==> tsnd t1'
| St_Snd_V : forall v1 v2,
    value v1 ->
    value v2 ->
    (tsnd (tpair v1 v2)) ==> v2
| St_Left : forall t1 t1',
    t1 ==> t1' ->
    tleft t1 ==> tleft t1'
| St_Right : forall t1 t1',
    t1 ==> t1' ->
    tright t1 ==> tright t1'
| ST_Case : forall t0 t0' x1 t1 x2 t2,
    t0 ==> t0' ->
    tcase t0 x1 t1 x2 t2 ==> tcase t0' x1 t1 x2 t2
| St_CaseL : forall v1 x1 t1 x2 t2,
    value v1 ->
    tcase (tleft v1) x1 t1 x2 t2 ==> [x1:=v1]t1
| St_CaseR : forall v2 x1 t1 x2 t2,
    value v2 ->
    tcase (tright v2) x1 t1 x2 t2 ==> [x2:=v2]t2
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(* From SfLib:
  Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
      R x y -> multi R y z -> multi R x z.
*)

Hint Constructors step.
Notation multistep := (multi step).
Notation "t1 '==>*' t2" := (multistep t1 t2) (at level 40).

Notation idBB := (tabs x (TArrow TBool TBool) (tvar x)).
Notation idB  := (tabs x TBool (tvar x)).                   

Lemma step_example1 :
  (tapp idBB idB) ==>* idB.
Proof.
  eapply multi_step.
  apply St_AppAbs.
  apply v_abs.
  simpl.
  apply multi_refl.
Qed.

Tactic Notation "print_goal" := match goal with |- ?x => idtac x end.
Tactic Notation "normalize" :=
   repeat (print_goal; eapply multi_step ;
             [ (eauto 10; fail) | (instantiate; simpl)]);
   apply multi_refl.

Lemma step_example2 :
  (tapp idBB idB) ==>* idB.
Proof.
  normalize.
Qed.

Lemma step_example3 :
  (tcase (tleft ttrue) x (tvar x) y (tvar y)) ==>* ttrue.
Proof.
  normalize.
Qed.

Module PartialMap.
  Definition partial_map (A:Type) := id -> option A.

  Definition empty {A:Type} : partial_map A := (fun _ => None).

  Definition extend {A:Type} (Gamma : partial_map A) (x:id) (T : A) :=
    fun x' => if eq_id_dec x x' then Some T else Gamma x'.

  Lemma extend_eq : forall A (ctxt: partial_map A) x T,
      (extend ctxt x T) x = Some T.
  Proof.
    intros.
    unfold extend.
    rewrite eq_id.
    reflexivity.
  Qed.

  Lemma extend_neq : forall A (ctxt : partial_map A) x1 T x2,
      x2 <> x1 ->
      (extend ctxt x2 T) x1 = ctxt x1.
  Proof.
    intros.
    unfold extend.
    rewrite neq_id; auto.
  Qed.

End PartialMap.

Definition context := partial_map ty.

Reserved Notation "G '|-' t '\in' T" (at level 40).

Inductive has_type : context -> tm -> ty -> Prop :=
| T_Var : forall G x T,
    G x = Some T -> G |- tvar x \in T
| T_Nat : forall G n,
    G |- tnum n \in TInt
| T_True : forall G,
    G |- ttrue \in TBool
| T_False : forall G,
    G |- tfalse \in TBool
| T_Unit : forall G,
    G |- tunit \in TUnit           
(* NO channles for now *)
| T_Pair : forall G t1 T1 t2 T2,
    G |- t1 \in T1 ->
    G |- t2 \in T2 ->
    G |- tpair t1 t2 \in TPair T1 T2
| T_InLeft : forall G t1 T1 T2,
    G |- t1 \in T1 ->
    G |- tleft t1 \in TSum T1 T2
| T_InRight : forall G T1 t2 T2,
    G |- t2 \in T2 ->
    G |- tright t2 \in TSum T1 T2
| T_Abs : forall G x T11 T12 t12,
    extend G x T11 |- t12 \in T12 ->
    G |- tabs x T11 t12 \in TArrow T11 T12
| T_App : forall T11 T12 G t1 t2,
    G |- t1 \in TArrow T11 T12 ->
    G |- t2 \in T11 ->
                G |- tapp t1 t2 \in T12
| T_Fst : forall G t1 T1 T2,
    G |- t1 \in TPair T1 T2 ->
    G |- tfst t1 \in T1
| T_Snd : forall G t1 T1 T2,
    G |- t1 \in TPair T1 T2 ->
    G |- tsnd t1 \in T2            
| T_If : forall G t1 t2 t3 T,
    G |- t1 \in TBool ->
    G |- t2 \in T ->
    G |- t3 \in T ->
    G |- tif t1 t2 t3 \in T                          
| T_Case : forall G t0 x1 t1 x2 t2 T1 T2 T,
    G |- t0 \in TSum T1 T2 ->
    extend G x1 T1 |- t1 \in T ->
    extend G x2 T2 |- t2 \in T ->
    G |- tcase t0 x1 t1 x2 t2 \in T 

where "G '|-' t '\in' T" := (has_type G t T).

Hint Constructors has_type.

Example typing_example_1 :
  empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.

Example typing_example_2 :
  empty |- tcase (tleft ttrue) x (tvar x) y (tvar y) \in TBool.
Proof.
  apply T_Case with (T1:=TBool)(T2:=TBool);
  repeat auto; apply T_Var; reflexivity.
Qed.

Example fail_typing_1 :
  ~ exists T, empty |- (tabs x TBool (tabs y TBool (tapp (tvar x) (tvar y)))) \in T.
Proof.
  intros Hc.
  inversion Hc.
  inversion H. subst.
  inversion H5. subst.
  inversion H6. subst.
  inversion H3. subst.
  inversion H2.
Qed.

Theorem progress: forall T t,
    empty |- t \in T ->
    value t \/ exists t', t ==> t'.               
Proof.
  intros.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  induction H; intros HeqGamma; subst.
  Case "Var".
  inversion H.
  Case "Num".
  left. auto.
  Case "True".
  left. auto.
  Case "False".
  left. auto.
  Case "Unit".
  left. auto.
  Case "Pair".
  destruct IHhas_type1. auto.
  destruct IHhas_type2; repeat auto.
  inversion H2.
  right. eauto.
  right. inversion H1. eauto.
  Case "Left".
  destruct IHhas_type. auto.
  left. auto.
  right. inversion H0 as [t1'].
  eauto.
  Case "Right".
  destruct IHhas_type.
  auto. left.  auto.
  right. inversion H0 as [t1']. eauto.
  Case "Abs".
  left. auto.  
  Case "App".
  destruct IHhas_type1. auto. subst.
  destruct IHhas_type2. auto.
    inversion H; subst; try (solve by inversion). (* Because who needs canonical forms. *)
    right. exists ([x0:=t2]t12).
    auto.
    right. inversion H2. eauto.
    right. inversion H1. eauto.
  Case "Fst".
    right.
    destruct IHhas_type. auto.
    inversion H; subst; try (solve by inversion).
    inversion H0. subst.
    exists t0. eauto.
    inversion H0 as [t1']. eauto.
  Case "Snd".
    right.
    destruct IHhas_type. auto.
    inversion H; subst; try (solve by inversion).
    inversion H0. subst.
    exists t2. eauto.
    inversion H0 as [t1']. eauto.
  Case "If".
    right.
    destruct IHhas_type1.
    auto.
    inversion H2; subst; try (solve by inversion).
    eauto.
    eauto.
    inversion H2 as [t1']. eauto.
  Case "Case".
    right.
    destruct IHhas_type1.
    inversion H; repeat auto.
    inversion H2; subst; try (solve by inversion).
    eauto.
    eauto.
    inversion H2 as [t1']. eauto.
Qed.

(* Substitution lemma pain *)

Inductive free_in : id -> tm -> Prop :=
| afi_var   : forall x, free_in x (tvar x)
| afi_appl  : forall x t1 t2, free_in x t1 -> free_in x (tapp t1 t2) 
| afi_appr  : forall x t1 t2, free_in x t2 -> free_in x (tapp t1 t2)
| afi_abs   : forall x y T1 t1, x <> y -> free_in x t1 -> free_in x (tabs y T1 t1)
| afi_if1   : forall x t1 t2 t3, free_in x t1 -> free_in x (tif t1 t2 t3)
| afi_if2   : forall x t1 t2 t3, free_in x t2 -> free_in x (tif t1 t2 t3)
| afi_if3   : forall x t1 t2 t3, free_in x t3 -> free_in x (tif t1 t2 t3)
| afi_pairl : forall x t1 t2, free_in x t1 -> free_in x (tpair t1 t2)
| afi_pairr : forall x t1 t2, free_in x t2 -> free_in x (tpair t1 t2)
| afi_fst   : forall x t1, free_in x t1 -> free_in x (tfst t1)
| afi_snd   : forall x t1, free_in x t1 -> free_in x (tsnd t1)
| afi_left  : forall x t1, free_in x t1 -> free_in x (tleft t1)
| afi_right : forall x t1, free_in x t1 -> free_in x (tright t1)
| afi_case0 : forall x t0 x1 t1 x2 t2, free_in x t0 -> free_in x (tcase t0 x1 t1 x2 t2)
| afi_case1 : forall x t0 x1 t1 x2 t2, x <> x1 -> free_in x t1 -> free_in x (tcase t0 x1 t1 x2 t2)
| afi_case2 : forall x t0 x1 t1 x2 t2, x <> x2 -> free_in x t2 -> free_in x (tcase t0 x1 t1 x2 t2).                                                               

Hint Constructors free_in.

Lemma context_invariance : forall G G' t S,
    G |- t \in S ->
    (forall x, free_in x t -> G x = G' x) ->
    G' |- t \in S.
Proof with eauto.
  intros. generalize dependent G'.
  induction H; try (intros G' Heqv; auto).
  Case "var".
    apply T_Var.
    rewrite <- Heqv...
  Case "abs".
    apply T_Abs.
    apply IHhas_type.
    intros y Hafi.
    unfold extend.
    destruct (eq_id_dec x0 y).
    reflexivity.
    rewrite <- Heqv. reflexivity.
    apply afi_abs... 
  Case "app".
    apply T_App with (T11:=T11).
    apply IHhas_type1.
    intros. apply Heqv...
    apply IHhas_type2.
    intros. apply Heqv... 
  Case "fst".
    apply T_Fst with (T2:=T2)...
  Case "snd".
    apply T_Snd with (T1:=T1)...
  Case "case".
    apply T_Case with (T1:=T1) (T2:=T2).
    SCase "case1".
    apply IHhas_type1.
    intros y Hafi.
    apply Heqv...
    SCase "case2".
    apply IHhas_type2.
    intros y Hafi.
    unfold extend. destruct (eq_id_dec x1 y)...    
    SCase "case3".
    apply IHhas_type3.
    intros y Hafi.
    unfold extend. destruct(eq_id_dec x2 y)... 
Qed.

Lemma free_in_context : forall x t T G,
  free_in x t ->
  G |- t \in T ->
  exists T', G x = Some T'.
Proof with eauto.             
  intros x t T G Hafi Htyp.
  induction Htyp; inversion Hafi; subst...
  Case "abs".
    destruct IHHtyp as [T' Hctx]... exists T'. 
    unfold extend in Hctx.
    rewrite neq_id in Hctx... 
  Case "case".
    SCase "left".
      destruct IHHtyp2 as [T' Hctx]... exists T'.
      unfold extend in Hctx.
      rewrite neq_id in Hctx... 
    SCase "right".
    destruct IHHtyp3 as [T' Hctx]. auto.
    exists T'.
    unfold extend in Hctx.
    rewrite neq_id in Hctx...
Qed.

Lemma subst_preserves_types : forall G x U v t S,
    (extend G x U) |- t \in S ->
    empty |- v \in U ->
    G |- ([x:=v]t) \in S.
Proof with eauto.
  intros G x U v t S Htypt Htypv.
  generalize dependent G. generalize dependent S.
  induction t; intros S G Htypt; simpl; inversion Htypt; subst; eauto.
  Case "Var".
    destruct (eq_id_dec x i).
    SCase "x=y".
      subst. unfold extend in H1. rewrite eq_id in H1.
      inversion H1; subst.
      eapply context_invariance. eauto.
      intros x Hcontra.
      destruct (free_in_context _ _ S empty Hcontra) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      unfold extend in H1. rewrite neq_id in H1.
      apply T_Var. assumption.
      assumption.
  Case "abs".
    rename i into y. rename t into T1. rename T12 into T2.
    apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      intros z Hafi. subst. unfold extend.
      destruct (eq_id_dec y z). reflexivity. reflexivity.
      SCase "x<>y".
      apply IHt.
      eapply context_invariance...
      intros z Hafi. unfold extend.
      destruct (eq_id_dec y z). subst. rewrite neq_id. reflexivity. assumption.
      reflexivity.
  Case "case".
    rename i into x1. rename i0 into x2.
    eapply T_Case...
      SCase "left arm".
        destruct (eq_id_dec x x1).
        SSCase "x = x1".
          eapply context_invariance...
          subst.
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x1 z)...
        SSCase "x <> x1".
          apply IHt2.
          eapply context_invariance...
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x1 z)...
          subst. rewrite neq_id. reflexivity.
          assumption.
      SCase "right arm".
        destruct (eq_id_dec x x2).
        SSCase "x = x2".
          eapply context_invariance...
          subst.
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x2 z)...
        SSCase "x <> x2".
          apply IHt3.
          eapply context_invariance...
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x2 z)...
          subst. rewrite neq_id. reflexivity.
          assumption.
Qed.

(* Preservation *)
Theorem preservation : forall t t' T,
    empty |- t \in T ->
    t ==> t' ->
    empty |- t' \in T.
Proof with eauto.
  intros t t' T HT.
  remember (@empty ty) as G.
  generalize dependent HeqG.
  generalize dependent t'.
  induction HT; intros t' HeqG HE; subst; inversion HE; subst...
  Case "app".
  inversion HE.
    SCase "St_AppAbs".
      subst.
      apply subst_preserves_types with T11.
      inversion HT1.
      eauto.
      auto.
    SCase "St_AppL".
      subst. eauto.
    SCase "St_AppR".
      subst. eauto.
  Case "fst".
    inversion HT; subst; eauto.
  Case "snd".
    inversion HT; subst; eauto.
  Case "case".
    SCase "St_CaseL".
      inversion HT1. subst.
      apply subst_preserves_types with T1. assumption. assumption.
    SCase "St_CaseR".
      inversion HT1. subst.
      apply subst_preserves_types with T2. assumption. assumption.
Qed.

Definition normal_form {X:Type} (R:relation X) (t:X) : Prop :=
  ~ exists t', R t t'.

Notation step_normal_form := (normal_form step).

Definition stuck (t:tm) : Prop :=
  step_normal_form t /\ ~ value t.

Hint Unfold stuck.

Definition halts (t:tm) : Prop := exists t', t ==>* t' /\ value t'.

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  apply multi_refl.
  assumption.
Qed.

Corollary soundness: forall t t' T,
    empty |- t \in T ->
    t ==>* t' ->
    ~(stuck t').
Proof.
  intros t t' T hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot_val]. unfold normal_form in Hnf.
  induction Hmulti.
  apply progress in hhas_type.
  destruct hhas_type.
  apply Hnot_val in H. assumption.
  apply Hnf in H. assumption.
  apply preservation with (T:=T) in H.
  apply IHHmulti in H.
  assumption.
  assumption.
  assumption.
  assumption.
Qed.
(* 
Lemma step_deterministic:
  deterministic step.
Proof with eauto.
  unfold deterministic.
  intros t1 t2 t2' lstep rstep.
  inversion lstep.
*)
            