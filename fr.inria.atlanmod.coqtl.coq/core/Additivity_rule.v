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
(** * Additivity in Rule context                             *)
(*************************************************************)

Definition Transformation_incl_rules'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  forall r: Rule, In r (Transformation_getRules t1) -> In r (Transformation_getRules t2). 

Theorem additivity_rules :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules'' t1 t2 -> 
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
  exists x0.
  split.
  + apply filter_In.
    split; auto.
  + auto.
Qed.