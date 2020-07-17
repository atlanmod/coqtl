(**

 CoqTL user theorem: Attribute_information_preservation

 Def: all non-derived attributes in the source model will create 
      collumn in the target model with the same name

 Proved with engine implementation

 **)

Require Import String.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import examples.Class2Relational.Theorems.Concrete_attributes_instantiate_impl.


Theorem Attribute_information_preservation_impl :
  forall (rm : Model RelationalMetamodel_EObject RelationalMetamodel_ELink)
    (cm: Model ClassMetamodel_EObject ClassMetamodel_ELink),
    rm = execute Class2Relational cm ->
    forall (a: Attribute),
      In (ClassMetamodel_toEObject a) (allModelElements cm) ->
      getAttributeDerived a = false ->
      exists (c: Column),
        In (RelationalMetamodel_toEObject c) (allModelElements rm) /\
        getColumnName c = getAttributeName a.
Proof.
  intros.
  rewrite H. clear H.
  destruct (Concrete_attributes_instantiate_impl cm a H1) as [c H].
  exists c.
  split.
  -   unfold execute. simpl.
      apply in_flat_map.
      exists ([ClassMetamodel_toEObject a]). split.
      + apply tuples_up_to_n_incl_length.
        * unfold incl. crush.
        * unfold instantiatePattern in H0.
          destruct (matchPattern Class2Relational cm [ClassMetamodel_toEObject a]) eqn:mtch.
          ** crush.
          ** unfold matchPattern in mtch.
             assert (In r (r::l)). { crush. }
             rewrite <- mtch in H2.
             apply filter_In in H2. destruct H2.
             destruct (matchRuleOnPattern r cm [ClassMetamodel_toEObject a]) eqn:mtch2.
             *** destruct b eqn: b_ca.
                  **** unfold matchRuleOnPattern in mtch2.
                       unfold evalGuard in mtch2.
                       unfold Expressions.evalFunction in mtch2.
                       assert (Expressions.evalFunctionFix _ _ _ _ ClassMetamodel (Syntax.Rule_getInTypes r) bool (Syntax.Rule_getGuard r cm) [ClassMetamodel_toEObject a] <> None).
                       { crush. }
                       apply Expressions.evalFunctionFix_intypes_el_neq_contraposition in H4.
                       apply tr_maxArity_in in H2.
                       crush.
                  **** crush.
          *** crush.
      + crush.
  - unfold instantiatePattern in H. unfold matchPattern in H. simpl in H.
    rewrite H1 in H. simpl in H.
    unfold instantiateRuleOnPattern in H. simpl in H.
    rewrite H1 in H. simpl in H.
    unfold instantiateIterationOnPattern in H. simpl in H.
    rewrite H1 in H. simpl in H.
    unfold instantiateElementOnPattern in H. simpl in H.
    rewrite H1 in H. simpl in H.
    unfold RelationalMetamodel_toEObjectOfEClass in H.
    unfold RelationalMetamodel_toEObject in H.
    unfold RelationalMetamodel_toEObjectFromColumn in H.
    assert (RelationalMetamodel_BuildEObject ColumnClass
             (BuildColumn (getAttributeId a) (getAttributeName a)) = 
            RelationalMetamodel_BuildEObject ColumnClass c).
    { crush. }
    apply rel_invert in H2.
    rewrite <- H2.
    simpl.
    reflexivity.
Qed.
