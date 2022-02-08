Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.
Require Import FunctionalExtensionality.


(*************************************************************)
(** * Confluence                                             *)
(*************************************************************)


Definition well_form  {tc: TransformationConfiguration} tr :=
  forall r1 r2 sm sp, 
    In r1 tr /\ In r2 tr/\
    matchRuleOnPattern r1 sm sp = true /\
    matchRuleOnPattern r2 sm sp = true ->
      r1 = r2.

(* Multiset semantics: we think that the list of rules represents a multiset/bag*)
(* Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  forall (r:Rule),
  count_occ' Rule_eqdec (Transformation_getRules t1) r = count_occ' Rule_eqdec (Transformation_getRules t2) r. *)

(* another way to represent multiset semantics*)
(* Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2) /\ 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2).*)

(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)
Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  set_eq (Transformation_getRules t1) (Transformation_getRules t2) /\
  well_form (Transformation_getRules t1) /\ 
  well_form (Transformation_getRules t2).

Lemma trace_eq {tc: TransformationConfiguration} :
  forall  t1 t2 sm,
   Transformation_equiv t1 t2 ->
   (trace t1 sm) = (trace t2 sm).
Proof.
  intros.
  destruct t1.
  destruct t2.
  induction l.
  - unfold Transformation_equiv in H.
    admit.
Admitted. 


Definition TargetModel_equiv {tc: TransformationConfiguration} (m1 m2: TargetModel) :=
  forall (e: TargetModelElement) (l: TargetModelLink),
   (In e (allModelElements m1) <-> In e (allModelElements m2)) /\
    (In l (allModelLinks m1) <-> In l (allModelLinks m2)).
  
Theorem confluence :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
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
                 assert (trace t1 sm = trace t2 sm). {
                   unfold trace, tracePattern.
                   admit. (* requires reordering for rules *)
                 }
Admitted.
