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

Definition Rule_incl_elements {tc: TransformationConfiguration} (x y: Rule) : Prop :=
  Rule_getName x = Rule_getName y
  /\ Rule_getGuardExpr x = Rule_getGuardExpr y  
  /\ Rule_getIteratorExpr x = Rule_getIteratorExpr y
  /\ (forall o1, In o1 (Rule_getOutputPatternElements x) -> In o1 (Rule_getOutputPatternElements y)).

Definition Transformation_incl_elements'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  (forall (r1: Rule), In r1 (Transformation_getRules t1) -> 
    (exists r2:Rule, In r2 (Transformation_getRules t2) /\ Rule_incl_elements r1 r2 )). 

Theorem additivity_elements_correct :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements'' t1 t2 -> 
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
  unfold Rule_incl_elements in H4.
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

  



