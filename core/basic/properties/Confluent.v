Require Import core.basic.basicSemantics.
Require Import core.basic.basicSyntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import core.basic.basicExpressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.

Section iConfluence.
Context (tc: TransformationConfiguration).


Definition well_form  {tc: TransformationConfiguration} tr :=
  forall r1 r2 sm sp, 
    In r1 tr /\ In r2 tr/\
    matchRuleOnPattern r1 sm sp = true /\
    matchRuleOnPattern r2 sm sp = true ->
      r1 = r2.


(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)

Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  set_eq (Transformation_getRules t1) (Transformation_getRules t2) /\
  well_form (Transformation_getRules t1) /\ 
  well_form (Transformation_getRules t2)
.

Definition TargetModel_equiv {tc: TransformationConfiguration} (m1 m2: TargetModel) :=
  forall (e: TargetModelElement) (l: TargetModelLink),
   (In e (allModelElements m1) <-> In e (allModelElements m2)) /\
    (In l (allModelLinks m1) <-> In l (allModelLinks m2)).



Lemma resolveIter_eq :
forall  t1 t2,
 Transformation_equiv t1 t2 ->
   resolveIter t1 = resolveIter t2.
Proof.
intros t1 t2 tr_eq.
unfold resolveIter.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
rename x into sm.
rename x1 into sp.
rename x2 into iter.
rename x0 into opname.

remember (fun r : Rule =>
matchRuleOnPattern r sm sp) as find_cond.
remember (Transformation_getRules t1) as rs1.
remember (Transformation_getRules t2) as rs2.

assert (find find_cond rs1 = find find_cond rs2).
{
  destruct (find find_cond rs1) eqn: find_ca1.
  destruct (find find_cond rs2) eqn: find_ca2.
  + apply find_some in find_ca1.
  apply find_some in find_ca2.
  f_equal.
  unfold Transformation_equiv in tr_eq.
  destruct tr_eq.
  destruct H0.
  assert (In r rs2). { unfold set_eq in H0. destruct H0. unfold incl in H0. crush. }
  destruct find_ca2.
  destruct find_ca1.
  rewrite Heqfind_cond in H6.
  rewrite Heqfind_cond in H4.
  destruct H1.
  unfold well_form in H7.
  specialize (H7 r r0 sm sp).
  crush.
  + apply find_some in find_ca1.
    specialize (find_none find_cond rs2 find_ca2).
    intro.
    unfold Transformation_equiv in tr_eq.
    destruct tr_eq.
    destruct H0.
    assert (In r rs2). { unfold set_eq in H1. destruct H1. unfold incl in H0. crush. }
    specialize (H r H0). crush.
  + destruct (find find_cond rs2) eqn: find_ca2.
  ++ apply find_some in find_ca2.
     specialize (find_none find_cond rs1 find_ca1).
     intro.
     unfold Transformation_equiv in tr_eq.
     destruct tr_eq.
     destruct H0.
     assert (In r rs1). { unfold set_eq in H1. destruct H1. unfold incl in H0. crush. }
     specialize (H r H0). crush.
  ++ auto.
}
rewrite H.
reflexivity.
Qed.

Theorem confluence :
forall  (t1 t2: Transformation) (sm: SourceModel),
  Transformation_equiv t1 t2 -> TargetModel_equiv (execute t1 sm) (execute t2 sm).
Proof.
  unfold TargetModel_equiv.
  unfold Transformation_equiv.
  simpl.
  intros.
  destruct H.
  split.
  - split.
    + unfold instantiatePattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- assumption.
    +  unfold instantiatePattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- assumption.
  - split.
    + unfold applyPattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- unfold applyRuleOnPattern, applyIterationOnPattern in *.
           apply in_flat_map in H3. repeat destruct H3.
           apply in_flat_map.
           exists x1.
           split.
           ++ assumption.
           ++ apply in_flat_map in H5. repeat destruct H5.
              apply in_flat_map.
              exists x2.
              split.
              ** assumption.
              ** unfold applyElementOnPattern in *. 
assert (resolveIter t1 = resolveIter t2).
{ apply resolveIter_eq. unfold Transformation_equiv. crush. }
destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
*** rewrite H7 in H6.
    auto.
*** auto.

+ unfold applyPattern.
      unfold matchPattern.
      intros.
      apply in_flat_map in H1. repeat destruct H1.
      apply in_flat_map in H2. repeat destruct H2.
      apply filter_In in H2. destruct H2.
      apply in_flat_map. exists x. split.
      * unfold allTuples.
        unfold maxArity.
        rewrite H.
        assumption.
      * apply in_flat_map.
        exists x0.
        split.
        -- apply filter_In.
           split.
           apply H0. assumption.
           assumption.
        -- unfold applyRuleOnPattern, applyIterationOnPattern in *.
           apply in_flat_map in H3. repeat destruct H3.
           apply in_flat_map.
           exists x1.
           split.
           ++ assumption.
           ++ apply in_flat_map in H5. repeat destruct H5.
              apply in_flat_map.
              exists x2.
              split.
              ** assumption.
              ** unfold applyElementOnPattern in *. 
assert ((resolveIter t1 = (resolveIter t2))).
{ apply resolveIter_eq. unfold Transformation_equiv. crush. }
destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
*** rewrite <- H7 in H6.
    auto.
*** auto.
Qed.

End iConfluence.
