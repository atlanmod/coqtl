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
(** * Monotonicity                                           *)
(*************************************************************)

Definition SourceModel_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2) /\
  incl (allModelLinks m1) (allModelLinks m2).

Definition TargetModel_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2) /\
  incl (allModelLinks m1) (allModelLinks m2).

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  SourceModel_incl sm1 sm2 -> TargetModel_incl (execute t sm1) (execute t sm2).

Theorem monotonicity_lifting :
  forall (tc: TransformationConfiguration) 
  (sm: SourceModel) (tr: Transformation),
    Forall 
      (fun r => monotonicity tc (buildTransformation (Transformation_getArity tr) [ r ]))
      (Transformation_getRules tr) 
        -> monotonicity tc tr.
Proof.
  unfold monotonicity.
  intros.
  rewrite Forall_forall in H.
  unfold execute.
  unfold TargetModel_incl.
  split.
Abort.
