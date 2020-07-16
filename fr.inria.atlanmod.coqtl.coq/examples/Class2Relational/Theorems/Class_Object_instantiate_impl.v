(**

 CoqTL user theorem: Class_Object_instantiate

 Def: all objects in the source model will instantiate some element contained by the target element

 Proved with engine implementation

 **)

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
Require Import examples.Class2Relational.Theorems.All_classes_instantiate_impl.
Require Import examples.Class2Relational.Theorems.Concrete_attributes_instantiate_impl.

Require Import core.utils.CpdtTactics.

Theorem All_classes_instantiate_aux :
  forall (cm : ClassModel) (c: Class),
  exists (t: RelationalMetamodel_EObject),
    instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [t].
Proof.
  intros.
  specialize (All_classes_instantiate_impl cm c).
  intro.
  destruct H.
  eexists (RelationalMetamodel_toEObject x).
  auto.
Qed.

Theorem Concrete_attributes_instantiate_aux :
  forall (cm : ClassModel) (a: Attribute),
    getAttributeDerived a = false ->
    exists (c: RelationalMetamodel_EObject),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [c].
Proof.
  intros.
  specialize (Concrete_attributes_instantiate_impl cm a).
  intro.
  destruct H0. auto.
  eexists (RelationalMetamodel_toEObject x).
  auto.
Qed.

Theorem Class_Object_instantiate_impl :
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