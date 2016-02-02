Require Import SfLib.

Module ValCon.

(* Types *)
Inductive ty : Type :=
  | TBool  : ty
  | TInt   : ty
  | TUnit  : ty
  | TErr   : ty            
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
  | tchan  : id -> tm
  | tdelay : tm -> tm
  | tforce : tm -> tm                   
  | tapp   : tm -> tm -> tm
  | tabs   : id -> ty -> tm -> tm
  | tif    : tm -> tm -> tm -> tm
  | tpair  : tm -> tm -> tm
  | tfst   : tm -> tm
  | tsnd   : tm -> tm
  | tleft  : tm -> tm
  | tright : tm -> tm
  | tcase  : tm -> id -> tm -> id -> tm -> tm
  | tthrow : ty -> tm -> tm
  | tcatch : tm -> tm -> tm.

Tactic Notation "t_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "tvar"
  | Case_aux c "ttrue"
  | Case_aux c "tfalse"
  | Case_aux c "tnum"
  | Case_aux c "tunit"
  | Case_aux c "tdelay"
  | Case_aux c "tforce"           
  | Case_aux c "tapp"
  | Case_aux c "tabs"
  | Case_aux c "tif"
  | Case_aux c "tpair"
  | Case_aux c "tfst"
  | Case_aux c "tsnd"
  | Case_aux c "tleft"
  | Case_aux c "tright"
  | Case_aux c "tcase"
  | Case_aux c "tthrow"
  | Case_aux c "tcatch"
  ].

Definition x := (Id 0).
Definition y := (Id 1).
Definition z := (Id 2).
Hint Unfold x.
Hint Unfold y.
Hint Unfold z.

Inductive value : tm -> Prop :=
  | v_true  : value ttrue
  | v_false : value tfalse
  | v_num   : forall n, value (tnum n)
  | v_unit  : value tunit
  | v_chan  : forall n, value (tchan n)
  | v_pair  : forall v1 v2, value v1 -> value v2 -> value (tpair v1 v2)
  | v_left  : forall v, value v -> value (tleft v)
  | v_right : forall v, value v -> value (tright v)
  | v_abs   : forall x T t, value (tabs x T t)
  | v_delay : forall t, value (tdelay t).

Inductive thrown : tm -> Prop :=
  | t_thrown : forall v T, value v -> thrown (tthrow T v).

Inductive answer : tm -> Prop :=
  | answer_val : forall v, value v -> answer v
  | answer_throw : forall t, thrown t -> answer t.                                           

Hint Constructors value.
Hint Constructors thrown.
Hint Constructors answer.

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
  | tdelay t =>
     tdelay ([x:=s] t) (* Hmm... *)
  | tforce t =>
     tforce ([x:=s] t)
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
  | tthrow T t1 =>
    tthrow T ([x:=s] t1)
  | tcatch t1 t2 =>
    tcatch ([x:=s] t1) ([x:=s] t2)
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
| St_ForceV : forall v1,
    value v1 ->
    tforce v1 ==> v1
| St_Force : forall t1 t1',
    t1 ==> t1' ->
    tforce t1 ==> tforce t1'
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
| St_Tthrow : forall T t1 t1',
    t1 ==> t1' -> tthrow T t1 ==> tthrow T t1'
| St_TForce_Throw : forall t1,
    thrown t1 -> tforce t1 ==> t1
| St_Tapp_ThrownL : forall t1 t2,
    thrown t1 -> tapp t1 t2 ==> t1
| St_Tapp_ThrownR : forall t1 t2,
    value t1 -> thrown t2 -> tapp t1 t2 ==> t2
| St_Tif_Thrown : forall t1 t2 t3,
    thrown t1 -> tif t1 t2 t3 ==> t1
| St_TPair_ThrownL : forall t1 t2,
    thrown t1 -> tpair t1 t2 ==> t1
| St_TPair_ThrownR : forall t1 t2,
    value t1 -> thrown t2 -> tpair t1 t2 ==> t2
| St_TFst_Thrown : forall t1,
    thrown t1 -> tfst t1 ==> t1
| St_TSnd_Thrown : forall t1,
    thrown t1 -> tsnd t1 ==> t1                      
| St_TLeft_Thrown : forall t1,
    thrown t1 -> tleft t1 ==> t1
| St_TRight_Thrown : forall t1,
    thrown t1 -> tright t1 ==> t1                      
| St_TCase_Thrown : forall t0 x1 t1 x2 t2,
    thrown t0 -> tcase t0 x1 t1 x2 t2 ==> t0
| St_TThrow_Thrown : forall T t1,
    thrown t1 -> tthrow T t1 ==> t1
| St_TCatch_L : forall t1 t1' t2,
    t1 ==> t1' -> tcatch t1 t2 ==> tcatch t1' t2
| St_Tcatch_Thrown : forall t1 t2,
    thrown t1 -> tcatch t1 t2 ==> t1
| St_TCatch_R : forall v1 t2 t2',
    value v1 -> t2 ==> t2' -> tcatch v1 t2 ==> tcatch v1 t2'
| St_TCatch_Elim : forall v1 v2,
    value v1 -> value v2 -> tcatch v1 v2 ==> v2    
| St_TCatch_Catch : forall T t1 t2,
    value t1 -> value t2 -> tcatch t1 (tthrow T t2) ==> tapp t1 t2
where "t1 '==>' t2" := (step t1 t2).

Hint Constructors step.

(*
  | tvar   : id -> tm
  | ttrue  : tm
  | tfalse : tm
  | tnum   : nat -> tm
  | tunit  : tm
  | tchan  : nat -> tm
  | tdelay : tm -> tm
  | tforce : tm -> tm                   
  | tapp   : tm -> tm -> tm
  | tabs   : id -> ty -> tm -> tm
  | tif    : tm -> tm -> tm -> tm
  | tpair  : tm -> tm -> tm
  | tfst   : tm -> tm
  | tsnd   : tm -> tm
  | tleft  : tm -> tm
  | tright : tm -> tm
  | tcase  : tm -> id -> tm -> id -> tm -> tm.
*)

Inductive nostep : tm -> Prop :=
| NS_Delay_App : forall t1 t2,
   nostep (tapp (tdelay t1) t2)
| NS_Delay_If : forall t1 t2 t3,
    nostep (tif (tdelay t1) t2 t3)
| NS_Delay_Case : forall t0 x1 t1 x2 t2,
    nostep (tcase (tdelay t0) x1 t1 x2 t2)
| NS_Delay_Fst : forall t1,
    nostep (tfst (tdelay t1))
| NS_Delay_Snd : forall t1,
    nostep (tsnd (tdelay t1))
| NS_Delay_Left : forall t,
    nostep (tleft (tdelay t))
| NS_Delay_Right : forall t,
    nostep (tright (tdelay t))
| NS_If : forall t t2 t3,
    nostep t -> nostep (tif t t2 t3)
| NS_PairL : forall t1 t2,
    nostep t1 ->
    nostep (tpair t1 t2)
| NS_PairR : forall t1 t2,
    value t1 ->
    nostep t2 ->
    nostep (tpair t1 t2)
| NS_Left : forall t1,
    nostep t1 -> nostep (tleft t1)
| NS_Right : forall t,
    nostep t -> nostep (tright t)
| NS_Force : forall t1,
    nostep t1 ->
    nostep (tforce t1)
| NS_AppR : forall t1 t2,
    nostep t2 -> nostep (tapp t1 t2)
| NS_AppL : forall t1 t2,
    nostep t1 -> nostep (tapp t1 t2)
| NS_Fst : forall t1,
    nostep t1 -> nostep (tfst t1)
| NS_Snd : forall t1,
    nostep t1 -> nostep (tsnd t1)
| NS_Case : forall t0 x1 t1 x2 t2,
    nostep t0 ->
    nostep (tcase t0 x1 t1 x2 t2)
| NS_Throw : forall T t1,
    nostep t1 ->
    nostep (tthrow T t1)
| NS_Catch_L : forall t1 t2,
    nostep t1 ->
    nostep (tcatch t1 t2)
| NS_Catch_R : forall t1 t2,
    nostep t2 ->
    nostep (tcatch t1 t2).

Hint Constructors nostep.


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

Lemma step_example4 :
  (tforce (tapp (tabs x TInt (tvar x)) (tnum 5))) ==>* tnum 5.
Proof.
  normalize.
Qed.

Lemma step_example5 :
  (tapp (tabs x TInt
              (tdelay (tapp (tabs x TInt (tnum 5)) (tnum 6))))
        (tnum 6)) ==>* (tdelay (tapp (tabs x TInt (tnum 5)) (tnum 6))).
Proof.
  normalize.
 Qed.
    
Lemma step_example6 :
  (tapp (tabs x TInt (tvar x)) (tthrow TInt (tnum 5))) ==>* (tthrow TInt (tnum 5)).
Proof.
  normalize.
Qed.

Lemma step_example7:
  tcatch (tabs x TInt (tnum 10)) (tapp (tabs x TInt (tvar x)) (tthrow TInt (tnum 5)))
  ==>* (tnum 10).
Proof.
  eapply multi_step.
  apply St_TCatch_R.
  auto.
  apply St_Tapp_ThrownR.
  auto.
  auto.
  apply multi_step with (y:=(tapp (tabs x TInt (tnum 10)) (tnum 5))).
  apply St_TCatch_Catch.
  auto. auto.
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

Reserved Notation "G ',' D '|-' t '\in' T" (at level 40).

Inductive has_type : context -> context -> tm -> ty -> Prop :=
| T_Var : forall G D x T,
    G x = Some T -> G , D |- tvar x \in T
| T_Nat : forall G D n,
    G , D |- tnum n \in TInt
| T_True : forall G D,
    G , D |- ttrue \in TBool
| T_False : forall G D,
    G , D |- tfalse \in TBool
| T_Unit : forall G D,
    G , D |- tunit \in TUnit           
| T_Chan : forall G D x T,
    D x = Some T -> G , D |- tchan x \in TChan T       
| T_Pair : forall G D t1 T1 t2 T2,
    G , D |- t1 \in T1 ->
    G , D |- t2 \in T2 ->
    G , D |- tpair t1 t2 \in TPair T1 T2
| T_InLeft : forall G D t1 T1 T2,
    G , D |- t1 \in T1 ->
    G , D |- tleft t1 \in TSum T1 T2
| T_InRight : forall G D T1 t2 T2,
    G , D |- t2 \in T2 ->
    G , D |- tright t2 \in TSum T1 T2
| T_Delay : forall G D T1 t1,
    G , D |- t1 \in T1 ->
    G , D |- tdelay t1 \in T1
| T_Force : forall G D T1 t1,
    G , D |- t1 \in T1 ->
    G , D |- tforce t1 \in T1
| T_Abs : forall G D x T11 T12 t12,
    (extend G x T11) , D |- t12 \in T12 ->
    G , D |- tabs x T11 t12 \in TArrow T11 T12
| T_App : forall T11 T12 G D t1 t2,
    G , D |- t1 \in TArrow T11 T12 ->
    G , D |- t2 \in T11 ->
    G , D |- tapp t1 t2 \in T12
| T_Fst : forall G D t1 T1 T2,
    G , D |- t1 \in TPair T1 T2 ->
    G , D |- tfst t1 \in T1
| T_Snd : forall G D t1 T1 T2,
    G , D |- t1 \in TPair T1 T2 ->
    G , D |- tsnd t1 \in T2            
| T_If : forall G D t1 t2 t3 T,
    G , D |- t1 \in TBool ->
    G , D |- t2 \in T ->
    G , D |- t3 \in T ->
    G , D |- tif t1 t2 t3 \in T                          
| T_Case : forall G D t0 x1 t1 x2 t2 T1 T2 T,
    G , D |- t0 \in TSum T1 T2 ->
    (extend G x1 T1) , D |- t1 \in T ->
    (extend G x2 T2) , D |- t2 \in T ->
    G , D|- tcase t0 x1 t1 x2 t2 \in T 
| T_Throw : forall G D t1 T1 T2,
    G , D |- t1 \in T1 ->
    G , D |- tthrow T1 t1 \in T2
| T_Catch : forall G D t1 t2 T1 T2,
   G , D |- t1 \in TArrow T2 T1 ->
   G , D |- t2 \in T1 ->
   G , D |- tcatch t1 t2 \in T1
(* | T_Catch_Escape : forall G t1 t2 T1 T2,
    G |- t1 \in TArrow T2 T1 ->
    G |- t2 \in T1 ->
    ~ thrown t2 ->            
    G |- tcatch t1 t2 \in T1                        
| T_Catch_Thrown : forall G t1 T1 T2 v,
    G |- t1 \in TArrow T2 T1 ->
    G |- v \in T2 ->
    G |- tcatch t1 (tthrow v) \in T1
*)                                               
where "G ',' D '|-' t '\in' T" := (has_type G D t T).

Hint Constructors has_type.

Tactic Notation "has_type_cases" tactic(first) ident(c) :=
  first;
  [ Case_aux c "T_Var"    | Case_aux c "T_Nat" | Case_aux c "T_True"
  | Case_aux c "T_False"  | Case_aux c "T_Unit"
  | Case_aux c "T_Pair"
  | Case_aux c "T_InLeft" | Case_aux c "T_InRight"
  | Case_aux c "T_Delay"
  | Case_aux c "T_Force"
  | Case_aux c "T_Abs"
  | Case_aux c "T_App"
  | Case_aux c "T_Fst"
  | Case_aux c "T_Snd"
  | Case_aux c "T_If"
  | Case_aux c "T_Case"
  | Case_aux c "T_Throw"
  | Case_aux c "T_Catch"
  (* | Case_aux c "T_Catch_Escape"
  | Case_aux c "T_Catch_Thrown" *)          
  ]. 
                                     
Example typing_example_1 :
  empty , empty |- tabs x TBool (tvar x) \in TArrow TBool TBool.
Proof.
  apply T_Abs.
  apply T_Var.
  reflexivity.
Qed.

Example typing_example_2 :
  empty , empty |- tcase (tleft ttrue) x (tvar x) y (tvar y) \in TBool.
Proof.
  apply T_Case with (T1:=TBool)(T2:=TBool);
  repeat auto; apply T_Var; reflexivity.
Qed.

Example typing_example_3 :
  empty , empty |- tforce (tdelay (tnum 5)) \in TInt.
Proof.
  apply T_Force. apply T_Delay. apply T_Nat.
Qed.

Example typing_example_4 :
  empty , empty |- tcatch (tabs x TInt (tnum 10))
                          (tapp (tabs x TInt (tvar x)) (tthrow TInt (tnum 5))) \in TInt.
Proof.
  apply T_Catch with (T2:=TInt).
  apply T_Abs. apply T_Nat.
  apply T_App with (T11:=TInt).
  apply T_Abs. apply T_Var.
  auto.
  apply T_Throw with (T1:=TInt).
  auto.
Qed.

Example fail_typing_1 :
  ~ exists T, empty , empty |- (tabs x TBool (tabs y TBool (tapp (tvar x) (tvar y)))) \in T.
Proof.
  intros Hc.
  inversion Hc.
  inversion H. subst.
  inversion H6. subst.
  inversion H7. subst.
  inversion H4. subst.
  inversion H3.
Qed.

Theorem progress: forall T t,
    (exists D, empty , D |- t \in T) ->
    answer t \/ (exists t', t ==> t') \/ nostep t.               
Proof with (auto; eauto).
  intros.
  remember (@empty ty) as Gamma.
  generalize dependent HeqGamma.
  inversion H as [D H'].
  induction H'; intros HeqGamma; subst; try solve[left; auto].
  Case "T_Var".
    inversion H0.
  Case "T_Pair".
    destruct IHH'1...
    destruct IHH'2...
    inversion H0; subst; try solve [right; left; eauto].
    inversion H1; subst; try solve [right; left; eauto].
    left...
    inversion H0; subst.
    inversion H1...  inversion H3...
    right. left. exists t1...
    inversion H0... inversion H1...
  Case "T_InLeft".
    destruct IHH'...
    inversion H0; subst...
    inversion H0... inversion H1.
    right. left. exists (tleft x0)...
  Case "T_InRight".
    destruct IHH'...
    inversion H0; subst...
    inversion H0... inversion H1.
    right. left. exists (tright x0)...
   Case "T_Force".
     destruct IHH'...
     inversion H0; subst; right; left; exists t1...
     inversion H0; subst; right.
     inversion H1. left. exists (tforce x0)...
     right...
  Case "T_App".
    destruct IHH'1; auto; subst.
    destruct IHH'2...
    inversion H0; subst.
    destruct IHH'2...
    inversion H2; subst.
    inversion H1; subst; inversion H'1; subst; try (solve by inversion)...
    (* No canonical forms *)
    right; left; eauto.
    inversion H2... inversion H3...
    right; left; eauto.
    inversion H0... inversion H1...
  Case "T_Fst".
    destruct IHH'...
    inversion H0; subst; inversion H1; subst; try (solve by inversion)...
    inversion H0... inversion H1...
  Case "T_Snd".
    destruct IHH'...
    inversion H0; subst; inversion H1; subst; try (solve by inversion)...
    inversion H0... inversion H1...
  Case "T_If".
    right. 
    destruct IHH'1...
    inversion H0; subst; inversion H1; subst; try (solve by inversion)...
    inversion H0... inversion H1...
  Case "T_Case".
    destruct IHH'1...
    inversion H0; subst; inversion H1; subst; try (solve by inversion)...
    inversion H0... inversion H1...
  Case "T_Throw".
    destruct IHH'...
    inversion H0; subst.
    left...
    right; left; exists t1...
    inversion H0... inversion H1...
  Case "T_Catch".
    destruct IHH'1...
    inversion H0; subst.
    destruct IHH'2...
    inversion H2; subst.
    right; left...
    right; left. inversion H3...
    inversion H2... inversion H3...
    right; left; exists t1...
    inversion H0... inversion H1...
 Qed.

(* Substitution lemma pain *)

Inductive free_in : id -> tm -> Prop :=
| afi_var    : forall x, free_in x (tvar x)
| afi_appl   : forall x t1 t2, free_in x t1 -> free_in x (tapp t1 t2) 
| afi_appr   : forall x t1 t2, free_in x t2 -> free_in x (tapp t1 t2)
| afi_delay  : forall x t1, free_in x t1 -> free_in x (tdelay t1)
| afi_force  : forall x t1, free_in x t1 -> free_in x (tforce t1)
| afi_abs    : forall x y T1 t1, x <> y -> free_in x t1 -> free_in x (tabs y T1 t1)
| afi_if1    : forall x t1 t2 t3, free_in x t1 -> free_in x (tif t1 t2 t3)
| afi_if2    : forall x t1 t2 t3, free_in x t2 -> free_in x (tif t1 t2 t3)
| afi_if3    : forall x t1 t2 t3, free_in x t3 -> free_in x (tif t1 t2 t3)
| afi_pairl  : forall x t1 t2, free_in x t1 -> free_in x (tpair t1 t2)
| afi_pairr  : forall x t1 t2, free_in x t2 -> free_in x (tpair t1 t2)
| afi_fst    : forall x t1, free_in x t1 -> free_in x (tfst t1)
| afi_snd    : forall x t1, free_in x t1 -> free_in x (tsnd t1)
| afi_left   : forall x t1, free_in x t1 -> free_in x (tleft t1)
| afi_right  : forall x t1, free_in x t1 -> free_in x (tright t1)
| afi_case0  : forall x t0 x1 t1 x2 t2, free_in x t0 -> free_in x (tcase t0 x1 t1 x2 t2)
| afi_case1  : forall x t0 x1 t1 x2 t2, x <> x1 -> free_in x t1 -> free_in x (tcase t0 x1 t1 x2 t2)
| afi_case2  : forall x t0 x1 t1 x2 t2, x <> x2 -> free_in x t2 -> free_in x (tcase t0 x1 t1 x2 t2)
| afi_throw  : forall x T t, free_in x t -> free_in x (tthrow T t)
| afi_catch1 : forall x t1 t2, free_in x t1 -> free_in x (tcatch t1 t2)
| afi_catch2 : forall x t1 t2, free_in x t2 -> free_in x (tcatch t1 t2).                                                               

Hint Constructors free_in.

Lemma context_invariance : forall G D G' t S,
    G , D |- t \in S ->
    (forall x, free_in x t -> G x = G' x) ->
    G' , D |- t \in S.
Proof with eauto.
  intros. generalize dependent G'.
  induction H; try (intros G' Heqv; auto; eauto).
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
  Case "catch".
    eapply T_Catch...
Qed.

Lemma free_in_context : forall x t T G D,
  free_in x t ->
  G , D |- t \in T ->
  exists T', G x = Some T'.
Proof with eauto.             
  intros x t T G D Hafi Htyp.
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

Lemma thrown_not_val : forall t,
    thrown t -> ~ value t.
Proof.
  intros.
  induction t; try (inversion H); subst.
  intros Hv. inversion Hv.
Qed.

Lemma value_not_thrown : forall t,
    value t -> ~ thrown t.
Proof.
  intros.
  induction H; intros Ht; inversion Ht.
Qed.  
  
Lemma subst_preserves_thrown : forall x t v,
    value t -> thrown ([x := v] t) -> thrown t.
Proof with eauto.
  intros.
  induction t; try (solve by inversion).
Qed.

Lemma subst_preserves_types : forall G D x U v t S,
    (extend G x U) , D |- t \in S ->
    empty , D |- v \in U ->
    G , D |- ([x:=v]t) \in S.
Proof with eauto.
  intros G D x U v t S Htypt Htypv.
  generalize dependent G. generalize dependent D. generalize dependent S.
  induction t; intros S D Htypt G Htypv; simpl; inversion Htypv; subst; eauto.
  Case "Var".
    destruct (eq_id_dec x i).
    SCase "x=y".
      subst. unfold extend in H2. rewrite eq_id in H2.
      inversion H2; subst.
      eapply context_invariance. eauto.
      intros x free.
      destruct (free_in_context _ _ S empty D free) as [T' HT']...
      inversion HT'.
    SCase "x<>y".
      unfold extend in H2. rewrite neq_id in H2...
  Case "Abs".
    rename i into y. rename t into T1. rename T12 into T2.
    apply T_Abs.
    destruct (eq_id_dec x y).
    SCase "x=y".
      eapply context_invariance...
      intros z Hafi. subst. unfold extend.
      destruct (eq_id_dec y z)...
    SCase "x<>y".
      apply IHt.
      inversion Htypv; subst.
      eapply context_invariance. eauto.
      intros z Hafi.
      reflexivity.
      eapply context_invariance. eauto.
      intros z Hafi.
      unfold extend.
      destruct (eq_id_dec y z). subst. rewrite neq_id...
      auto.
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
          eapply context_invariance...
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x1 z)...
          subst. rewrite neq_id...
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
          eapply context_invariance...
          intros z Hafi.
          unfold extend.
          destruct (eq_id_dec x2 z)...
          subst. rewrite neq_id...
Qed.

(* Preservation *)
Theorem preservation : forall t t' T D,
    empty , D |- t \in T ->
    t ==> t' ->
    empty , D |- t' \in T.
Proof with (auto; eauto; subst).
  intros t t' T D HT.
  remember (@empty ty) as G.
  generalize dependent HeqG.
  generalize dependent t'.
  induction HT; intros t' HeqG HE; subst; inversion HE; subst;
  try solve [inversion HT; subst; eauto; inversion H0; inversion HT;
             subst; apply T_Throw with (T1:=T0)
            | inversion HT1; subst; eapply subst_preserves_types; auto; eauto]...
  Case "Pair".
  inversion H2...
  inversion H; subst; inversion HT1; subst; apply T_Throw with (T1:=T)...
  inversion H3; subst; inversion HT2; subst; apply T_Throw with (T1:=T)...
  Case "App".
  (* apply subst_preserves_types with T11... inversion HT1... *)
  inversion H2; subst; inversion HT1; subst; apply T_Throw with (T1:=T)...
  inversion H3; subst; inversion HT2; subst; apply T_Throw with (T1:=T)...
  Case "If".
  inversion H3; subst; inversion HT1; subst; apply T_Throw with (T1:=T0)...
  Case "Case_Thrown".
    inversion H5; subst; inversion HT1; subst; apply T_Throw with (T1:=T0)...
  Case "Throw".
    
  inversion HE; subst.
  apply T_Throw with (T1:=T1)...
  
    
    inversion H2; subst; inversion HT; subst; apply T_Throw with (T1:=T)...
  Case "Throw_R".
  inversion HT2; subst.
  apply T_App with (T11:=T2)...
  
  (* apply instantiate_thrown_type in HT2. *)
  inversion HT2; subst; try (solve by inversion); subst.
  inversion t3; try (solve by inversion)...
  inversion HT2 as [T3 HT3].
  
  inversion HT2; subst.
  inversion HT2; subst.
  apply T_App with (T11:=T2)...
    inversion H0; subst; inversion HT; subst; apply T_Throw with (T1:=T0)...
    inversion HT; subst; eauto.
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
  (step_normal_form t /\ ~ value t /\ ~ nostep t).
Hint Unfold stuck.

Definition halts (t:tm) : Prop := exists t', t ==>* t' /\ (value t' \/ nostep t').

Lemma value_halts : forall v, value v -> halts v.
Proof.
  intros v H. unfold halts.
  exists v. split.
  apply multi_refl.
  left. auto.
Qed.

Lemma value_unsteps : forall v, value v -> ~ exists t', v ==> t'.
Proof.
  intros v Hval.
  intros Hstep.
  induction v; try (solve by inversion); try (inversion Hstep; inversion H; subst).
  apply IHv1. inversion Hval. auto. eauto.
  apply IHv2. inversion Hval. auto. eauto.
  apply IHv. inversion Hval. auto. eauto.
  apply IHv. inversion Hval. auto. eauto.
Qed.

Lemma step_unvalue : forall t1 t2, t1 ==> t2 -> ~ (value t1).
Proof with (repeat auto).
  intros t1 t2 Hstep Hnot_val.
  generalize dependent t2.
  induction t1; intros;
    try (solve by inversion);
    try (inversion Hstep; inversion Hnot_val; subst).
  apply IHt1_1 with (t2:=t1')...
  apply IHt1_2 with (t2:=t2')...
  apply IHt1 with (t2:=t1')...
  apply IHt1 with (t2:=t1')...
Qed.  

(*
Lemma nostep_cant_step : forall t, nostep t -> ~ exists t', t ==>* t'.
Proof with eauto.
  intros t Hno_step ext.
  induction t; try (solve by inversion).
  Case "False".
  apply IHt.
  inversion Hno_step. assumption.
  inversion ext. exists x0.
  inversion H. subst.
  inversion Hnostep.
  Case "force".
  inversion ext as [t1 Hstep].
  inversion Hstep. subst.
  inversion Hno_step. subst.
*)

Corollary soundness : forall t t' T,
    empty |- t \in T ->
    t ==>* t' -> ~(stuck t').
Proof.
  intros t t' T hhas_type Hmulti. unfold stuck.
  intros [Hnf Hnot].
  destruct Hnot as [Hnot_val Hnot_nostep].
  unfold normal_form in Hnf.
  induction Hmulti.
  apply progress in hhas_type.
  destruct hhas_type.
  apply Hnot_val in H.
  assumption.
  destruct H.
  apply Hnf in H.
  assumption.
  apply Hnot_nostep in H.
  assumption.
  apply preservation with (T:=T) in H.
  apply IHHmulti in H.
  assumption.
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
            