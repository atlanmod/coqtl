Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Additivity in OutputPatternElement context             *)
(*************************************************************)

Definition Rule_incl_elements' {tc: TransformationConfiguration} (x y: Rule) : Prop :=
  Rule_getName x = Rule_getName y
  /\ Rule_getGuardExpr x = Rule_getGuardExpr y  
  /\ Rule_getIteratorExpr x = Rule_getIteratorExpr y
  /\ (forall o1, In o1 (Rule_getOutputPatternElements x) -> In o1 (Rule_getOutputPatternElements y)).

Definition Transformation_incl_elements''' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  (forall (r1: Rule), In r1 (Transformation_getRules t1) -> 
    (exists r2:Rule, In r2 (Transformation_getRules t2) /\ Rule_incl_elements' r1 r2 )). 

Theorem additivity_elements_general :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements''' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
simpl.
unfold incl.
intros.
apply in_flat_map in H0. repeat destruct H0. 
apply in_flat_map in H1. repeat destruct H1.
apply filter_In in H1. destruct H1.
destruct H.
apply in_flat_map. exists x.
split.
* unfold allTuples.
  unfold maxArity.
  rewrite <- H.
  assumption.
* apply in_flat_map.
  specialize (H4 x0 H1).
  destruct H4.
  exists x1.
  unfold Rule_incl_elements' in H4.
  destruct H4. destruct H5. destruct H6. destruct H7.
  split.
  + apply filter_In.
    split; auto.
    unfold matchRuleOnPattern, evalGuardExpr.
    unfold matchRuleOnPattern,evalGuardExpr in H3.
    rewrite <- H6. auto.
  + apply in_flat_map.
    apply in_flat_map in H2.
    destruct H2.
    exists x2.
    destruct H2.
    split.
    ++ unfold evalIteratorExpr; unfold evalIteratorExpr in H2. rewrite <- H7; auto.
    ++ apply in_flat_map; apply in_flat_map in H9.
       destruct H9. destruct H9.
       specialize (H8 x3 H9).
       exists x3.
       split; auto.
Qed.


Definition Rule_incl_elements {tc: TransformationConfiguration} (x y: Rule) : Prop :=
  Rule_getName x = Rule_getName y
  /\ Rule_getGuardExpr x = Rule_getGuardExpr y  
  /\ Rule_getIteratorExpr x = Rule_getIteratorExpr y
  /\ subseq (Rule_getOutputPatternElements x) (Rule_getOutputPatternElements y).

Inductive Transformation_incl_rules' {tc: TransformationConfiguration}  : list Rule -> list Rule -> Prop :=
  | incl_rules_nil : Transformation_incl_rules' nil nil
  | incl_rules_diff : forall x y xs ys, Transformation_incl_rules' xs ys 
    -> Rule_incl_elements x y
    -> Transformation_incl_rules' (x::xs) (y::ys).

Definition Transformation_incl_elements'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  Transformation_incl_rules' (Transformation_getRules t1) (Transformation_getRules t2). 

Lemma tr_incl_equiv:
  forall (tc: TransformationConfiguration) t1 t2,
    Transformation_incl_elements'' t1 t2 -> Transformation_incl_elements''' t1 t2.
Proof.
intros.
destruct  H.
unfold Transformation_incl_elements'''.
split. 
* auto.
* intro.
  induction H0.
  **  intros.
      contradiction.
  **  intros.
      simpl in H2.
      destruct H2.
      - exists y.
        split.
        -- crush.
        -- rewrite <- H2.
           unfold Rule_incl_elements in H1.
           unfold Rule_incl_elements'; crush.
           induction H6.
           --- contradiction.
           --- destruct H5; crush.
           --- crush.
      - specialize (IHTransformation_incl_rules' H2). 
        destruct IHTransformation_incl_rules'.
        destruct H3.
        exists x0; crush.
Qed.

Theorem additivity_elements_correct :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements'' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
intros.
specialize (tr_incl_equiv tc t1 t2 H).
specialize (additivity_elements_general tc t1 t2).
auto.
Qed.



