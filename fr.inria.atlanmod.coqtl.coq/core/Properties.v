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

Definition toTransformation (tc: TransformationConfiguration) (f: SourceModel -> TargetModel) := 
  (buildTransformation 0 [
    (buildRule "rule"%string 
      (fun sm sp => match sp with nil => Some true | _ => Some false end)
      (fun sm sp => Some (length (allModelElements (f sm))))
      [(buildOutputPatternElement "out"%string 
         (fun i sm sp => nth_error (allModelElements (f sm)) i)
         (fun tls i sm sp te => match i with 0 => Some (allModelLinks (f sm)) | _ => None end))
      ])
  ]).

Theorem universality :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  (forall (sm: SourceModel), Model_wellFormed sm -> Model_wellFormed (f sm)) ->
  exists (t: Transformation), 
    forall (sm: SourceModel), Model_wellFormed sm -> execute t sm = f sm.
Proof.
  intros.
  exists (toTransformation tc f).
  intros.
  unfold execute.
  unfold applyPattern.
  unfold applyRuleOnPattern.
  unfold applyIterationOnPattern.
  unfold applyElementOnPattern.
  unfold evalOutputPatternLinkExpr.
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  unfold instantiateIterationOnPattern.
  unfold instantiateElementOnPattern.
  unfold evalOutputPatternElementExpr.
  unfold evalIteratorExpr.
  unfold evalExpr.
  simpl.
  apply (H sm) in H0.
  destruct (f sm). simpl.
  f_equal.
  - clear H. clear H0.
    induction modelElements.
    * reflexivity.
    * simpl.
      f_equal.
      rewrite <- IHmodelElements at 2.
      repeat rewrite flat_map_concat_map.
      f_equal.
      rewrite <- seq_shift.
      rewrite map_map.
      reflexivity.
  - destruct modelElements eqn:dst.
    * crush. 
    * clear H0.
      simpl. 
      repeat rewrite app_nil_r.
      rewrite app_nil_end.
      f_equal.
      apply in_flat_map_nil.
      intros.
      rewrite app_nil_r.
      destruct a.
      + exfalso. 
        rewrite in_seq in H0.
        lia.
      + simpl.
        rewrite in_seq in H0.
        destruct H0.
        simpl in H1.
        apply Lt.lt_S_n in H1.
        destruct (nth_error l a); reflexivity.
Qed.

Definition Rule_eqdec: forall {tc: TransformationConfiguration}  (x y:Rule), {x = y} + {x <> y}.
Admitted.

(* Multiset semantics: we think that the list of rules represents a multiset/bag*)
Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  forall (r:Rule),
  count_occ' Rule_eqdec (Transformation_getRules t1) r = count_occ' Rule_eqdec (Transformation_getRules t2) r.

(* another way to represent multiset semantics*)
(* Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2) /\ 
  sub_set (Transformation_getRules t1) (Transformation_getRules t2).*)

(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)
Definition Transformation_equiv' {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  forall (r:Rule),
  In r (Transformation_getRules t1) <-> In r (Transformation_getRules t2).

Definition TargetModel_equiv {tc: TransformationConfiguration} (m1 m2: TargetModel) :=
  forall (e: TargetModelElement) (l: TargetModelLink),
   (In e (allModelElements m1) <-> In e (allModelElements m2)) /\
    (In l (allModelLinks m1) <-> In l (allModelLinks m2)).
  
Theorem confluence :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  Transformation_equiv' t1 t2 -> TargetModel_equiv (execute t1 sm) (execute t2 sm).
Proof.
  unfold TargetModel_equiv.
  unfold Transformation_equiv'.
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

Definition Model_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2) /\
  incl (allModelLinks m1) (allModelLinks m2).

Definition Transformation_incl_elements {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  forall (r1: Rule), In r1 (Transformation_getRules t1) ->
    (In r1 (Transformation_getRules t2) \/
     (exists (r2:Rule), 
       In r2 (Transformation_getRules t2) /\
         Rule_getName r1 = Rule_getName r2 /\
         Rule_getGuardExpr r1 = Rule_getGuardExpr r2 /\
         Rule_getIteratorExpr r1 = Rule_getIteratorExpr r2 /\
         incl (Rule_getOutputPatternElements r1) (Rule_getOutputPatternElements r2))).

(* Version with set semantics for rules*)
Theorem additivity_elements :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
  simpl.
  unfold incl.
  intros.
  apply in_flat_map in H0. repeat destruct H0. 
  apply in_flat_map in H1. repeat destruct H1.
  apply filter_In in H1. destruct H1.
  destruct H.
  apply in_flat_map. exists x.
  split.
  * unfold allTuples.
    unfold maxArity.
    rewrite <- H.
    assumption.
  * apply in_flat_map.
    pose (H4 x0).
    destruct o.
    + assumption.
    + exists x0.
      split.
      - unfold matchPattern.
        apply filter_In.
        split.
        ** assumption.
        ** assumption.
      - assumption.
    + destruct H5.
      exists x1.
      destruct H5, H6, H7, H8.  
      split.
      - unfold matchPattern.
        apply filter_In.
        split.
        ** assumption.
        ** unfold matchRuleOnPattern, evalGuardExpr. 
           rewrite <- H7.
           unfold matchRuleOnPattern, evalGuardExpr in H3.
           assumption.
      - unfold instantiateRuleOnPattern, evalIteratorExpr, instantiateIterationOnPattern.
        unfold instantiateRuleOnPattern, evalIteratorExpr, instantiateIterationOnPattern in H2.
        rewrite <- H8.
        apply in_flat_map in H2. repeat destruct H2. 
        apply in_flat_map. 
        exists x2.
        split.
        ** assumption.
        ** apply in_flat_map in H10. repeat destruct H10. 
            apply in_flat_map.
            exists x3.
            split.
            ++ unfold incl in H9.
               apply (H9 x3).
               assumption.
            ++ assumption. 
Qed.

Definition Transformation_incl_links {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  forall (r1: Rule), In r1 (Transformation_getRules t1) ->
    (In r1 (Transformation_getRules t2) \/
     (exists (r2:Rule),
       forall (o1: OutputPatternElement), In o1 (Rule_getOutputPatternElements r1) ->
         (In o1 (Rule_getOutputPatternElements r2) \/
          (exists (o2: OutputPatternElement), 
            In o2 (Rule_getOutputPatternElements r2) /\ 
              OutputPatternElement_getName o1 = OutputPatternElement_getName o2 /\
              OutputPatternElement_getElementExpr o1 = OutputPatternElement_getElementExpr o2 /\ 
              OutputPatternLink_getLinkExpr o2 = fun _ _ _ _ _ => None
            )))).

Theorem additivity_links :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_links t1 t2 -> 
    Model_incl (execute t1 sm) (execute t2 sm)).
Proof.
  simpl.
  unfold Model_incl.
  unfold incl.
  intros.
  split.
  --  intros.
      apply in_flat_map in H0. repeat destruct H0. 
      apply in_flat_map in H1. repeat destruct H1.
      apply filter_In in H1. destruct H1.
      destruct H.
      apply in_flat_map. exists x.
      split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        pose (H4 x0).
        destruct o.
        + assumption.
        + exists x0.
          split.
          - unfold matchPattern.
            apply filter_In.
            split.
            ** assumption.
            ** assumption.
          - assumption.
        + destruct H5.
          exists x1.
          admit.
  --  intros.
      apply in_flat_map in H0. repeat destruct H0. 
      apply in_flat_map in H1. repeat destruct H1.
      apply filter_In in H1. destruct H1.
      destruct H.
      apply in_flat_map. exists x.
      split.
      * unfold allTuples.
        unfold maxArity.
        rewrite <- H.
        assumption.
      * apply in_flat_map.
        pose (H4 x0).
        destruct o.
        + assumption.
        + exists x0.
          split.
          - unfold matchPattern.
            apply filter_In.
            split.
            ** assumption.
            ** assumption.
          - Admitted.

Definition SourceModel_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2) /\
  incl (allModelLinks m1) (allModelLinks m2).

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  SourceModel_incl sm1 sm2 -> Model_incl (execute t sm1) (execute t sm2).
