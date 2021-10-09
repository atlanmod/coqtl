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
  /\ subseq (Rule_getOutputPatternElements x) (Rule_getOutputPatternElements y).

Inductive Transformation_incl_rules' {tc: TransformationConfiguration}  : list Rule -> list Rule -> Prop :=
  | incl_rules_nil : Transformation_incl_rules' nil nil
  | incl_rules_diff : forall x y xs ys, Transformation_incl_rules' xs ys 
    -> Rule_incl_elements x y
    -> Transformation_incl_rules' (x::xs) (y::ys).

Definition Transformation_incl_elements'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  Transformation_incl_rules' (Transformation_getRules t1) (Transformation_getRules t2). 

Theorem additivity_elements_correct :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements'' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
intros tc t1 t2 sm tr_incl.
unfold incl.
intros e in_t1.
apply in_flat_map in in_t1. 
destruct in_t1.
destruct H.
apply in_flat_map in H0. repeat destruct H0.
apply filter_In in H0. destruct H0.
destruct tr_incl.
apply in_flat_map. exists x.
split.
* unfold allTuples.
  unfold maxArity. 
  rewrite <- H3.
  assumption.
* apply in_flat_map.
  destruct H4 eqn: tr_in_r_ca.
Admitted.
