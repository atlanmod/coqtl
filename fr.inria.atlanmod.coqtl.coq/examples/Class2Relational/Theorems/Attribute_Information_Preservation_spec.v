Require Import String.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.Certification.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Require Import examples.Class2Relational.Theorems.Concrete_attributes_instantiate_spec.
Require Import examples.Class2Relational.Theorems.Concrete_attributes_instantiate_impl.

(* with lemmas *)
Theorem Attribute_information_preservation_spec :
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
  destruct (Concrete_attributes_instantiate_spec cm a H1) as [c H].
  destruct c.
  destruct c.
  - simpl in r. rename r into t.
    apply tr_instantiatePattern_in in H.
    destruct H as [r [tp [Hmatch [Hinst Hin]]]].
    apply tr_matchPattern_in in Hmatch.
    destruct Hmatch as [Hr Hmatch].
    unfold matchRuleOnPattern' in Hmatch.
    rewrite tr_matchRuleOnPattern_eval in Hmatch.
    unfold Expressions.evalFunction in Hmatch.
    destruct Hr as [Hr | [Hr | Hfalse]].
    --  crush.
    --  rewrite <- Hr in Hinst. clear Hr.
        unfold instantiateRuleOnPattern in Hinst.
        simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
        unfold instantiateIterationOnPattern in Hinst.
        simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
        unfold instantiateElementOnPattern in Hinst.
        simpl in Hinst. rewrite H1 in Hinst. simpl in Hinst.
        inversion Hinst as [Htp]. clear Hinst.
        rewrite <- Htp in Hin. clear Htp.
        destruct a, t. simpl in *.
        destruct Hin as [Hte | Hfalse].
        * unfold RelationalMetamodel_toEObjectOfEClass in Hte.
          unfold RelationalMetamodel_toEObject in Hte.
          unfold RelationalMetamodel_toEObjectFromColumn in Hte.
          inversion Hte.
        * destruct Hfalse.
    -- crush. 
  - simpl in r.
    exists r.
    split.
    destruct H. destruct H.
    --  apply tr_execute_in_elements.
        exists ([ClassMetamodel_toEObject a]).
        exists x.
        repeat split.
        + apply incl_cons.
          * exact H0.
          * intros a' H'. destruct H'.
        + eassumption.
        + crush.
    --  rename H into H'. rename r into c.
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
