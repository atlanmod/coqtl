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

Theorem All_classes_instantiate :
  forall (cm : ClassModel) (c: Class),
  exists (t: Table),
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [RelationalMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.

Theorem All_classes_instantiate_aux :
  forall (cm : ClassModel) (c: Class),
  exists (t: RelationalMetamodel_EObject),
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [t].
Proof.
  intros.
  specialize (All_classes_instantiate cm c).
  intro.
  destruct H.
  eexists (RelationalMetamodel_toEObject x).
  auto.
Qed.

Theorem All_classes_instantiate' :
  forall (cm : ClassModel) (c: Class),
  exists (t: RelationalMetamodel_EObject) tp,
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some tp /\
    In t tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - left. reflexivity.
  - reflexivity.
  - left. reflexivity.
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

Theorem Concrete_attributes_instantiate_aux :
  forall (cm : ClassModel) (a: Attribute),
    getAttributeDerived a = false ->
    exists (c: RelationalMetamodel_EObject),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [c].
Proof.
  intros.
  specialize (Concrete_attributes_instantiate cm a).
  intro.
  destruct H0. auto.
  eexists (RelationalMetamodel_toEObject x).
  auto.
Qed.

Theorem Concrete_attributes_instantiate' :
  forall (cm : ClassModel) (a: Attribute),
    getAttributeDerived a = false ->
    exists (c: RelationalMetamodel_EObject) tp,
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some tp /\
      In c tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - apply tr_matchPattern_in.
    split.
    + right. left. reflexivity.
    + (* rewrite tr_matchRuleOnPattern. *)
      unfold matchRuleOnPattern'. unfold matchRuleOnPattern. unfold evalGuard.
      unfold Expressions.evalFunction. simpl. rewrite H. reflexivity.
  - (* rewrite tr_instantiateRuleOnPattern. *)
    unfold instantiateRuleOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateIterationOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateElementOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    simpl. reflexivity.
  - left. reflexivity.
Qed.

Theorem Class_Object_instantiate :
  forall (cm : ClassModel) (a: ClassMetamodel_EObject) (att: Attribute),
    ((ClassMetamodel_instanceOfEClass ClassEClass a = true) \/
         ((ClassMetamodel_toEClass AttributeEClass a = Some att) /\
              (getAttributeDerived att = false))) ->
    exists (c: RelationalMetamodel_EObject),
       instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [c].
Proof.
  intros.
  destruct H.
  + destruct (ClassMetamodel_toEClass ClassEClass a) eqn: a_ca.
    ++  assert ((ClassMetamodel_toEObject c) = a). { apply Class_Object_cast; auto. }
        rewrite <- H0.
        apply All_classes_instantiate_aux.
    ++  unfold ClassMetamodel_instanceOfEClass in H.
        unfold ClassMetamodel_toEClass in a_ca.
        destruct a.
        destruct (ClassMetamodel_eqEClass_dec c ClassEClass) eqn: c_ca.
        +++ crush.
        +++ simpl in H. rewrite c_ca in H. crush.
  + destruct H.
    assert ((ClassMetamodel_toEObject att) = a). { apply Attribute_Object_cast; auto. }
    rewrite <- H1.
    apply Concrete_attributes_instantiate_aux. exact H0.
Qed.

Theorem Class_Object_instantiate' :
  forall (cm : ClassModel) (a: ClassMetamodel_EObject) (att: Attribute),
    ((ClassMetamodel_instanceOfEClass ClassEClass a = true) \/
         ((ClassMetamodel_toEClass AttributeEClass a = Some att) /\
              (getAttributeDerived att = false))) ->
    exists (c: RelationalMetamodel_EObject) tp,
      instantiatePattern Class2Relational cm [a] = Some tp /\
      In c tp.
Proof.
  intros.
  destruct H.
  + destruct (ClassMetamodel_toEClass ClassEClass a) eqn: a_ca.
    ++  assert ((ClassMetamodel_toEObject c) = a). { apply Class_Object_cast; auto. }
        rewrite <- H0.
        apply All_classes_instantiate'.
    ++  unfold ClassMetamodel_instanceOfEClass in H.
        unfold ClassMetamodel_toEClass in a_ca.
        destruct a.
        destruct (ClassMetamodel_eqEClass_dec c ClassEClass) eqn: c_ca.
        +++ crush.
        +++ simpl in H. rewrite c_ca in H. crush.
  + destruct H.
    assert ((ClassMetamodel_toEObject att) = a). { apply Attribute_Object_cast; auto. }
    rewrite <- H1.
    apply Concrete_attributes_instantiate'. exact H0.
Qed.


