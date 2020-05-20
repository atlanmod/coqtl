
Require Import core.utils.TopUtils.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import examples.Class2Relational.Theorems.Basic_theorems.
(* Note: the engine version used in Basic_theorems must be the same used here *)


Theorem information_preservation :
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
