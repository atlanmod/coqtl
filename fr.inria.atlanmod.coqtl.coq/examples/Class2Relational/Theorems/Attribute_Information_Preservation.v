Require Import String.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import examples.Class2Relational.Theorems.Class2Relational_basic_theorems.
(* Note: the engine version used in Basic_theorems must be the same used here *)

(* w/o lemmas *)
Theorem Attribute_information_preservation :
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
  destruct (Concrete_attributes_instantiate cm a H1) as [c H].
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

(* with lemmas *)
Theorem information_preservation' :
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
  destruct (Concrete_attributes_instantiate cm a H1) as [c H].
  exists c.
  split.
  - apply tr_execute_in_elements.
    do 2 eexists (_ :: nil).
    repeat split.
    + apply incl_cons.
      * exact H0.
      * intros a' H'. destruct H'.
    + eassumption.
    + left. reflexivity.
  - assert (exists tp, instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = return tp /\ In (RelationalMetamodel_toEObject c) tp) as H'.
    {
      exists (RelationalMetamodel_toEObject c :: nil).
      split. assumption. left. reflexivity.
    }
    apply tr_instantiatePattern_in in H'.
    destruct H' as [r [tp [Hmatch [Hinst Hin]]]].
    apply tr_matchPattern_in in Hmatch.
    destruct Hmatch as [Hr Hmatch].
    unfold matchRuleOnPattern' in Hmatch.
    rewrite tr_matchRuleOnPattern_eval in Hmatch.
    unfold Expressions.evalFunction in Hmatch.
    destruct Hr as [Hr | [Hr | Hfalse]].
    + rewrite <- Hr in Hmatch.
      simpl in Hmatch. discriminate Hmatch.
    + rewrite <- Hr in Hinst. clear Hr.
      unfold instantiateRuleOnPattern in Hinst.
      simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
      unfold instantiateIterationOnPattern in Hinst.
      simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
      unfold instantiateElementOnPattern in Hinst.
      simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
      inversion Hinst as [Htp]. clear Hinst.
      rewrite <- Htp in Hin. clear Htp.
      destruct a, c. simpl in *.
      destruct Hin as [Hte | Hfalse].
      * unfold RelationalMetamodel_toEObjectOfEClass in Hte.
        unfold RelationalMetamodel_toEObject in Hte.
        unfold RelationalMetamodel_toEObjectFromColumn in Hte.
        apply rel_invert in Hte.
        inversion Hte.
        reflexivity.
      * destruct Hfalse.
    + destruct Hfalse.
Qed.
