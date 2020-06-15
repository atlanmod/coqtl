Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import core.utils.CpdtTactics.

Theorem All_classes_match_spec :
  forall (cm : ClassModel) (c : Class),
  exists (r : Rule ClassMetamodel RelationalMetamodel),
    In r (matchPattern Class2Relational cm [ClassMetamodel_toEObject c]).
Proof.
  intros.
  eexists.
  apply tr_matchPattern_in.
  split.
  - left. reflexivity.
  - (* rewrite tr_matchRuleOnPattern. *)
    unfold matchRuleOnPattern'.
    unfold matchRuleOnPattern.
    unfold evalGuard.
    unfold Expressions.evalFunction. simpl. reflexivity.
Qed.