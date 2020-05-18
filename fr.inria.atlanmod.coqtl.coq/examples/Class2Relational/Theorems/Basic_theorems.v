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

Theorem All_classes_match :
  forall (cm : ClassModel) (c : Class),
  exists (r : Rule ClassMetamodel RelationalMetamodel),
    matchPattern Class2Relational cm [ClassMetamodel_toEObject c] = [r].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.

Theorem All_classes_match' :
  forall (cm : ClassModel) (c : Class),
  exists (r : Rule ClassMetamodel RelationalMetamodel),
    In r (matchPattern Class2Relational cm [ClassMetamodel_toEObject c]).
Proof.
  intros.
  eexists _.
  apply tr_matchPattern_in.
  split.
  - left. reflexivity.
  - (* rewrite tr_matchRuleOnPattern. *)
    unfold matchRuleOnPattern'.
    unfold matchRuleOnPattern.
    unfold evalGuard.

    unfold Expressions.evalFunction. simpl. reflexivity.
Qed.

Theorem All_classes_instantiate :
  forall (cm : ClassModel) (c: Class),
  exists (t: Table),
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [RelationalMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.

Theorem Concrete_attributes_instantiate :
  forall (cm : ClassModel) (a: Attribute),
    getAttributeDerived a = false ->
    exists (c: Column),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [RelationalMetamodel_toEObject c].
Proof.
  intros.
  eexists _.
  unfold instantiatePattern. unfold matchPattern. simpl.
  rewrite H. simpl.
  unfold instantiateRuleOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateIterationOnPattern. simpl.
  rewrite H. simpl.
  unfold instantiateElementOnPattern. simpl.
  rewrite H. simpl.
  reflexivity.
Qed.
