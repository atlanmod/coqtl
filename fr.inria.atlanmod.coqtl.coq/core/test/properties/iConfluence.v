Require Import core.test.iSemantics.
Require Import core.test.iSyntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import core.test.iExpressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Confluence                                             *)
(*************************************************************)

(* Multiset semantics: we think that the list of rules represents a multiset/bag*)
(* Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  forall (r:Rule),
  count_occ' Rule_eqdec (Transformation_getRules t1) r = count_occ' Rule_eqdec (Transformation_getRules t2) r. *)

(* another way to represent multiset semantics*)
(* Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2) /\ 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2).*)


Section iConfluence.
Context (tc: TransformationConfiguration).


(* a rule is well formed if all its outpatternname are different *)

(* if a well formed rule r1 is not in tr, then all r0 in tr, r0's outpatternname are different from r1 *)


(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)
Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  set_eq (Transformation_getRules t1) (Transformation_getRules t2) /\
  NoDup (Transformation_getRules t1) /\ 
  NoDup (Transformation_getRules t2)
.

Definition TargetModel_equiv {tc: TransformationConfiguration} (m1 m2: TargetModel) :=
  forall (e: TargetModelElement) (l: TargetModelLink),
   (In e (allModelElements m1) <-> In e (allModelElements m2)) /\
    (In l (allModelLinks m1) <-> In l (allModelLinks m2)).


Lemma rule_nodup_imply_trace_nodup:
forall  t1 sm,
 NoDup (Transformation_getRules t1) ->
   NoDup (trace t1 sm).
Proof.
intros.
unfold trace.
unfold tracePattern.
unfold matchPattern.
induction (Transformation_getRules t1).
+ simpl. 
  induction ((allTuples t1 sm)).
  ++  simpl. apply NoDup_nil.
  ++ simpl. auto.
+ apply NoDup_cons_iff in H. destruct H.
  specialize (IHl H0).




Admitted.

Lemma tr_set_eq_imply_trace_eq :
forall  t1 t2 sm,
 Transformation_equiv t1 t2 -> 
   set_eq (trace t1 sm) (trace t2 sm).
Proof.
intros t1 t2 sm treq.
repeat split.
+ unfold Transformation_equiv in treq.
  destruct treq. destruct H0. 
  clear H1. (* they probably not useful *)
  unfold set_eq in H0.
  destruct H0.
  unfold incl in *.
  intros.
  apply (in_flat_map) in H2.
  destruct H2 as [sp sp_cond].
  destruct sp_cond.
  apply (in_flat_map).
  exists sp.
  split. 
  ++  unfold allTuples in *.
      unfold maxArity in *.
      rewrite <- H. exact H2.
  ++  apply (in_flat_map) in H3.
      apply (in_flat_map).
      destruct H3.
      exists x.
      split.
      * destruct H3.
        unfold matchPattern in *.
        apply filter_In.
        apply filter_In in H3.
        destruct H3.
        specialize (H0 x).
        split; crush.
      * crush.
+ unfold Transformation_equiv in treq.
  destruct treq. destruct H0. 
  clear H1. (* they probably not useful *)
  unfold set_eq in H0.
  destruct H0.
  unfold incl in *.
  intros.
  apply (in_flat_map) in H2.
  destruct H2 as [sp sp_cond].
  destruct sp_cond.
  apply (in_flat_map).
  exists sp.
  split. 
  ++  unfold allTuples in *.
      unfold maxArity in *.
      rewrite H. exact H2.
  ++  apply (in_flat_map) in H3.
      apply (in_flat_map).
      destruct H3.
      exists x.
      split.
      * destruct H3.
        unfold matchPattern in *.
        apply filter_In.
        apply filter_In in H3.
        destruct H3.
        specialize (H0 x).
        split; crush.
      * crush.
Qed.

Lemma tr_set_eq_imply :
forall  t1 t2 sm,
 Transformation_equiv t1 t2 ->
   NoDup (trace t1 sm) /\
   NoDup (trace t2 sm) /\ 
   set_eq (trace t1 sm) (trace t2 sm).
Proof.
intros t1 t2 sm treq.
split.
+ apply rule_nodup_imply_trace_nodup. unfold Transformation_equiv in treq. crush.
+ split.
  ++ apply rule_nodup_imply_trace_nodup. unfold Transformation_equiv in treq. crush.
  ++ apply tr_set_eq_imply_trace_eq. crush.
Qed.

Lemma resolveIter_eq :
forall  t1 t2 sm,
 Transformation_equiv t1 t2 ->
   resolveIter (trace t1 sm) = resolveIter (trace t2 sm).
Proof.
intros t1 t2 sm tr_eq.
unfold resolveIter.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.

remember ((fun tl0 : TraceLink =>
        (iSemantics.list_beq SourceModelElement SourceElement_eqb
           (TraceLink_getSourcePattern tl0) x1 && (TraceLink_getIterator tl0 =? x2) &&
         (TraceLink_getName tl0 =? x0)%string)%bool)) as tr_filter.

remember ((filter tr_filter (trace t1 sm))) as fl1.
remember ((filter tr_filter (trace t2 sm))) as fl2.

specialize (tr_set_eq_imply t1 t2 sm tr_eq). intro.

assert (length fl1 = length fl2). { specialize (filter_mutual_length_eq (trace t1 sm) (trace t2 sm)). crush. }

destruct (Datatypes.length fl1) eqn: l1_length.
+ rewrite <- H0. auto.
+ rewrite <- H0.
  destruct n; auto.
  - 
destruct H.
destruct H1.
apply (NoDup_filter tr_filter) in H. rewrite <- Heqfl1 in H.
apply (NoDup_filter tr_filter) in H1. rewrite <- Heqfl2 in H1.
specialize (incl_filter_mutual (trace t1 sm) (trace t2 sm) H2 tr_filter). intro. rewrite <- Heqfl1 in H3. rewrite <- Heqfl2 in H3.
specialize (set_eq_imply_nth_error_eq fl1 fl2 H H1 H3 l1_length).
intro.
rewrite H4.
auto.
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
assert ((resolveIter (trace t1 sm) = (resolveIter (trace t2 sm)))).
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
assert ((resolveIter (trace t1 sm) = (resolveIter (trace t2 sm)))).
{ apply resolveIter_eq. unfold Transformation_equiv. crush. }
destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
*** rewrite <- H7 in H6.
    auto.
*** auto.
Qed.

End iConfluence.
