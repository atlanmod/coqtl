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

 

(*********************************************************)
(** * Additivity in OutputPatternLink context            *)
(*********************************************************)

Fixpoint Rule_incl_patternElements {tc: TransformationConfiguration} (l1 l2: list OutputPatternElement) : Prop :=
  match l1, l2 with
  | o1 :: l1', o2 :: l2' => 
      OutputPatternElement_getName o1 = OutputPatternElement_getName o2 
      /\ OutputPatternElement_getElementExpr o1 = OutputPatternElement_getElementExpr o2
      /\ (OutputPatternElement_getLinkExpr o1 = OutputPatternElement_getLinkExpr o2 \/ 
          OutputPatternElement_getLinkExpr o1 = (fun _ _ _ _ _ => None))
      /\ Rule_incl_patternElements l1' l2'
  | nil, nil => True
  | _, _ => False
  end.

Lemma Rule_incl_patternElements_exists:
  forall (tc: TransformationConfiguration) opes1 opes2 o1,
    Rule_incl_patternElements opes1 opes2 -> In o1 opes1 ->
      (exists o2, In o2 opes2 /\ 
         OutputPatternElement_getName o1 = OutputPatternElement_getName o2 
      /\ OutputPatternElement_getElementExpr o1 = OutputPatternElement_getElementExpr o2
      /\ (OutputPatternElement_getLinkExpr o1 = OutputPatternElement_getLinkExpr o2 \/ 
          OutputPatternElement_getLinkExpr o1 = (fun _ _ _ _ _ => None)) ).
Proof.
intros.
revert H.
revert opes2.
revert H0.
induction opes1.
- contradiction.
- intros.
  simpl in H0.
  destruct H0.
  --  unfold Rule_incl_patternElements in H.
      destruct opes2.
      + contradiction.
      + exists o.
      split; crush.
  --  induction opes2.
      + unfold Rule_incl_patternElements in H.
        contradiction.
      + clear IHopes2.
        assert (Rule_incl_patternElements opes1 opes2).
        {
        unfold Rule_incl_patternElements.
        unfold Rule_incl_patternElements in H.
        crush.
        }
        specialize (IHopes1 H0 opes2 H1).
        destruct IHopes1.
        destruct H2.
        exists x.
        split; auto.
        simpl.
        right.
        auto.
Qed.


Fixpoint Transformation_incl_rules {tc: TransformationConfiguration} (l1 l2: list Rule) : Prop :=
  match l1, l2 with
  | r1 :: l1', r2 :: l2' => 
      Rule_getName r1 = Rule_getName r2
      /\ Rule_getGuardExpr r1 = Rule_getGuardExpr r2  
      /\ Rule_getIteratorExpr r1 = Rule_getIteratorExpr r2
      /\ Rule_incl_patternElements (Rule_getOutputPatternElements r1) (Rule_getOutputPatternElements r2) 
      /\ Transformation_incl_rules l1' l2'
  | nil, nil => True
  | _, _ => False
  end.

Definition Transformation_incl_links {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  (Transformation_incl_rules (Transformation_getRules t1) (Transformation_getRules t2)). 

Definition Model_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2) /\
  incl (allModelLinks m1) (allModelLinks m2).


Lemma Transformation_incl_rules_exists:
  forall (tc: TransformationConfiguration) (rs1 rs2: list Rule) (r1: Rule),
    Transformation_incl_rules rs1 rs2 -> In r1 rs1 ->
      (exists r2, In r2 rs2 /\ 
         Rule_getName r1 = Rule_getName r2
      /\ Rule_getGuardExpr r1 = Rule_getGuardExpr r2  
      /\ Rule_getIteratorExpr r1 = Rule_getIteratorExpr r2
      /\ Rule_incl_patternElements (Rule_getOutputPatternElements r1) (Rule_getOutputPatternElements r2) ).
Proof.
intros.
revert H.
revert rs2.
revert H0.
induction rs1.
- contradiction.
- intros.
  simpl in H0.
  destruct H0.
  --  unfold Transformation_incl_rules in H.
      destruct rs2.
      + contradiction.
      + exists r.
      split; crush.
  --  induction rs2.
      + unfold Transformation_incl_rules in H.
        contradiction.
      + clear IHrs2.
        assert (Transformation_incl_rules rs1 rs2).
        {
        unfold Transformation_incl_rules.
        unfold Transformation_incl_rules in H.
        crush.
        }
        specialize (IHrs1 H0 rs2 H1).
        destruct IHrs1.
        destruct H2.
        exists x.
        split; auto.
        simpl.
        right.
        auto.
Qed.

Lemma Rule_incl_patternElements_eq:
  forall  (tc: TransformationConfiguration)  x x0 sm opes1 opes2,
   Rule_incl_patternElements opes1 opes2 ->
    flat_map
  (fun o : OutputPatternElement =>
   optionToList
     (e <- evalOutputPatternElementExpr sm x x0 o;
      return buildTraceLink (x, x0, OutputPatternElement_getName o) e)) opes1 = 
  flat_map
  (fun o : OutputPatternElement =>
   optionToList
     (e <- evalOutputPatternElementExpr sm x x0 o;
      return buildTraceLink (x, x0, OutputPatternElement_getName o) e)) opes2.
Proof.
intros.
revert H.
revert opes2.
induction opes1.
- intros.
  unfold Rule_incl_patternElements in H.
  destruct opes2.
  -- auto.
  -- contradiction.
- induction opes2.
  -- intros.
     unfold Rule_incl_patternElements in H.
     contradiction.
  -- clear IHopes2.
     intros.

     assert (Rule_incl_patternElements opes1 opes2). {
       unfold Rule_incl_patternElements in H.
       unfold Rule_incl_patternElements.
       crush.
     }
     specialize (IHopes1 opes2 H0).
     simpl.

     assert (optionToList
       (e <- evalOutputPatternElementExpr sm x x0 a;
       return buildTraceLink (x, x0, OutputPatternElement_getName a) e) =
        optionToList
       (e <- evalOutputPatternElementExpr sm x x0 a0;
       return buildTraceLink (x, x0, OutputPatternElement_getName a0) e)). 
      {
      f_equal.
      unfold Rule_incl_patternElements in H.
      destruct H.
      destruct H1.
      clear H2.
      unfold evalOutputPatternElementExpr.
      rewrite H.
      rewrite H1.
      auto.
      }

     crush.
Qed.

Lemma matchPattern_eq:
  forall (tc: TransformationConfiguration)  t1 t2 sm x,
  Transformation_incl_links t1 t2 ->
    flat_map (fun r : Rule => traceRuleOnPattern r sm x)
      (matchPattern t1 sm x) = 
    flat_map (fun r : Rule => traceRuleOnPattern r sm x)
      (matchPattern t2 sm x).
Proof.
intros.
revert H.
destruct t1 as [a1 rs1].
revert t2.
induction rs1.
- (* base case: rs1 = nil *)
  intros.
  unfold Transformation_incl_links in H.
  simpl in H.
  destruct H.
  destruct (Transformation_getRules t2) eqn: t2_res.
  -- (* case 1: rs2 = nil *)
     unfold trace.
     unfold tracePattern.
     destruct t2.
     simpl in t2_res.
     rewrite t2_res.
     simpl.
     auto.
  -- (* case 2: rs2 != nil, a contradiction w.r.t. Transformation_incl_links *)
     contradiction.
- intro.
  destruct t2 as [a2 rs2].
  induction rs2.
  -- (* base case: rs2 = nil, a contradiction w.r.t. Transformation_incl_links *)
     intro.
     unfold Transformation_incl_links in H.
     simpl in H.
     destruct H.
     contradiction.
  -- specialize (IHrs1 (buildTransformation a2 rs2)).
     intros.
     assert (Transformation_incl_links (buildTransformation a1 rs1)
              (buildTransformation a2 rs2) ).  (* derived from H *)
     { 
      unfold Transformation_incl_links in H. 
      unfold Transformation_incl_links.
      crush.
     }

     specialize (IHrs1 H0).
      clear IHrs2.

      unfold Transformation_incl_links in H. 
      simpl in H.
      destruct H.
      destruct H1.
      destruct H2.
      destruct H3.
      destruct H4.


      unfold matchPattern.
      simpl.

      destruct (matchRuleOnPattern a sm x) eqn: ca1.
      + destruct (matchRuleOnPattern a0 sm x) eqn: ca2.
        ++ simpl.
      assert (traceRuleOnPattern a sm x = traceRuleOnPattern a0 sm x).
      { unfold traceRuleOnPattern.
        unfold evalIteratorExpr.
        rewrite H3.
        unfold traceIterationOnPattern, traceElementOnPattern, instantiateElementOnPattern.

        f_equal.
        apply functional_extensionality.
        intros.

        remember  (Rule_getOutputPatternElements a) as opes1.
        remember  (Rule_getOutputPatternElements a0) as opes2.

        apply Rule_incl_patternElements_eq.
        auto.
       }
      rewrite H6.
      assert (flat_map (fun r : Rule => traceRuleOnPattern r sm x)
        (filter (fun r : Rule => matchRuleOnPattern r sm x) rs1) = 
      flat_map (fun r : Rule => traceRuleOnPattern r sm x)
        (filter (fun r : Rule => matchRuleOnPattern r sm x) rs2)).
      {  unfold matchPattern in IHrs1. simpl in IHrs1. auto. }
      rewrite H7.
      auto.
        ++ unfold matchRuleOnPattern in ca2.
           unfold evalGuardExpr in ca2.
           rewrite <- H2 in ca2.
           unfold matchRuleOnPattern in ca1.
           unfold evalGuardExpr in ca1.
           crush. (* contradiction in ca1 and ca2 *) 
      + destruct (matchRuleOnPattern a0 sm x) eqn: ca2.
        ++ unfold matchRuleOnPattern in ca2.
           unfold evalGuardExpr in ca2.
           rewrite <- H2 in ca2.
           unfold matchRuleOnPattern in ca1.
           unfold evalGuardExpr in ca1.
           crush. (* contradiction in ca1 and ca2 *)
        ++ unfold matchPattern in IHrs1.
           simpl in IHrs1.
           auto.
Qed.


Lemma trace_eq:
  forall (tc: TransformationConfiguration)  t1 t2 sm,
  Transformation_incl_links t1 t2 ->
    (trace t1 sm) = (trace t2 sm).
Proof.
intros.
revert H.
destruct t1 as [a1 rs1].
revert t2.
induction rs1.
- (* base case: rs1 = nil *)
  intros.
  unfold Transformation_incl_links in H.
  simpl in H.
  destruct H.
  destruct (Transformation_getRules t2) eqn: t2_res.
  -- (* case 1: rs2 = nil *)
     unfold trace.
     unfold tracePattern.
     destruct t2.
     simpl in t2_res.
     rewrite t2_res.
     simpl.
     unfold allTuples.
     unfold maxArity.
     simpl.
     simpl in H.
     rewrite H.
     auto.
  -- (* case 2: rs2 != nil, a contradiction w.r.t. Transformation_incl_links *)
     contradiction.
- (* inductive case: rs1 *)
  intro.
  destruct t2 as [a2 rs2].
  induction rs2.
  -- (* base case: rs2 = nil, a contradiction w.r.t. Transformation_incl_links *)
     intro.
     unfold Transformation_incl_links in H.
     simpl in H.
     destruct H.
     contradiction.
  -- (* inductive case: rs2 = nil *)
     specialize (IHrs1 (buildTransformation a2 rs2)).
     intros.

     assert (Transformation_incl_links (buildTransformation a1 rs1)
              (buildTransformation a2 rs2) ).  (* derived from H *)
     { 
      unfold Transformation_incl_links in H. 
      unfold Transformation_incl_links.
      crush.
     }

     specialize (IHrs1 H0).
     unfold trace, tracePattern.
     f_equal.
     + (* traceRuleOnPattern on matchPattern of t1 and t2 are the same *)
       apply functional_extensionality.
       intros.
       apply matchPattern_eq.
       auto.
     + (* allTuples of t1 and t2 are the same *)
       unfold allTuples.
       simpl.
       unfold Transformation_incl_links in H0.
       destruct H0.
       simpl in H0.
       rewrite H0.
       auto.
Qed.

Theorem additivity_links:
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_links t1 t2 -> 
    Model_incl (execute t1 sm) (execute t2 sm)).
Proof.
  simpl.
  unfold Model_incl.
  unfold incl.
  unfold Transformation_incl_links.
intros.
split.
- intro.
  simpl.
  destruct H.
  intros.
  apply in_flat_map in H1 as [sp].
  destruct H1.
  apply in_flat_map in H2 as [r1].
  destruct H2.
  apply in_flat_map in H3 as [iter1].
  destruct H3.
  apply in_flat_map in H4 as [ope].
  destruct H4.
  unfold instantiateElementOnPattern in H5.
  destruct (evalOutputPatternElementExpr sm sp iter1 ope) eqn: outExpr.
  + simpl in H5.
    destruct H5.
    ++ apply in_flat_map.
exists sp.
assert ((allTuples t1 sm) = (allTuples t2 sm)) as allTup. { 
  unfold allTuples.
  unfold maxArity.
  rewrite H.
  auto.
}
split.
+++ rewrite <- allTup. exact H1.
+++ apply in_flat_map.
    specialize (Transformation_incl_rules_exists tc (Transformation_getRules t1) (Transformation_getRules t2) r1 H0).
    intros.
    assert (In r1 (Transformation_getRules t1)). { unfold matchPattern in H2. apply filter_In in H2. destruct H2. exact H2. }
    specialize (H6 H7).
    repeat destruct H6.
    destruct H8.
    destruct H8.
    rename x into r2.
    exists r2.
    split.
    ++++  unfold matchPattern in H2.
          apply filter_In in H2.
          unfold matchPattern.
          apply filter_In.
          split.
          * auto.
          * destruct H2.
            unfold matchRuleOnPattern, evalGuardExpr.
          unfold matchRuleOnPattern, evalGuardExpr in H8.
          destruct H9.
          rewrite <- H9.
          auto.
    ++++  apply in_flat_map.
          exists iter1.
          split.
          +++++ unfold evalIteratorExpr.
                unfold evalIteratorExpr in H3.
                destruct H9.
                destruct H9.
                rewrite <- H9.
                auto.
          +++++ unfold instantiateIterationOnPattern.
                unfold instantiateElementOnPattern.
                assert (exists ope2, In ope2 (Rule_getOutputPatternElements r2) /\ evalOutputPatternElementExpr sm sp iter1 ope2 = return a).
                {
                destruct H9.
                destruct H9.
                specialize Rule_incl_patternElements_exists.
                intros.
                specialize (H11 tc (Rule_getOutputPatternElements r1) (Rule_getOutputPatternElements r2)).
                specialize (H11 ope H10 H4).
                destruct H11.
                destruct H11.
                destruct H12.
                destruct H13.
                clear H14.
                exists x.
                split; auto.
                unfold evalOutputPatternElementExpr.
                unfold evalOutputPatternElementExpr in outExpr.
                rewrite <- H13.
                rewrite <- H5.
                auto.
                }
                destruct H8.
                apply in_flat_map.
                exists x.
                split.
                * destruct H8.
                  auto.
                * destruct H8.
                rewrite H10.
                simpl.
                left.
                auto.
    ++ contradiction.
  + contradiction.
- intro.
  simpl.
  destruct H.
  intros.
  apply in_flat_map in H1 as [sp].
  destruct H1.
  apply in_flat_map in H2 as [r1].
  destruct H2.
  apply in_flat_map in H3 as [iter1].
  destruct H3.
  apply in_flat_map in H4 as [ope].
  destruct H4.
  unfold applyElementOnPattern in H5.
  destruct (evalOutputPatternElementExpr sm sp iter1 ope) eqn: outExpr.
  + destruct (evalOutputPatternLinkExpr sm sp t iter1 (trace t1 sm) ope) eqn: linkExpr.
    ++ simpl in H5.
       apply in_flat_map.
       exists sp.
       assert ((allTuples t1 sm) = (allTuples t2 sm)) as allTup. { 
        unfold allTuples.
        unfold maxArity.
        rewrite H.
        auto.
       }
       split.
       +++  rewrite <- allTup. exact H1.
       +++  apply in_flat_map.
            specialize (Transformation_incl_rules_exists tc (Transformation_getRules t1) (Transformation_getRules t2) r1 H0).
            intros.
            assert (In r1 (Transformation_getRules t1)). { unfold matchPattern in H2. apply filter_In in H2. destruct H2. exact H2. }
            specialize (H6 H7).
            repeat destruct H6.
            destruct H8.
            destruct H8.
            rename x into r2.
            exists r2.
            split.
            ++++  unfold matchPattern in H2.
                  apply filter_In in H2.
                  unfold matchPattern.
                  apply filter_In.
                  split.
                  * auto.
                  * destruct H2.
                    unfold matchRuleOnPattern, evalGuardExpr.
                  unfold matchRuleOnPattern, evalGuardExpr in H8.
                  destruct H9.
                  rewrite <- H9.
                  auto.
            ++++  apply in_flat_map.
                  exists iter1.
                  split.
                  +++++ unfold evalIteratorExpr.
                        unfold evalIteratorExpr in H3.
                        destruct H9.
                        destruct H9.
                        rewrite <- H9.
                        auto.
                  +++++ assert ((trace t1 sm) = (trace t2 sm)).
                        { 
                          apply trace_eq.
                          unfold Transformation_incl_links; auto.
                        }
                        unfold applyIterationOnPattern.
                        unfold applyElementOnPattern.
                        assert (exists ope2, In ope2 (Rule_getOutputPatternElements r2) /\ 
                                  evalOutputPatternElementExpr sm sp iter1 ope2 = return t /\
                                  evalOutputPatternLinkExpr sm sp t iter1 (trace t1 sm) ope2 = return l).
                        {
                        destruct H9.
                        destruct H9.
                        destruct H10.
                        specialize Rule_incl_patternElements_exists.
                        intros.
                        specialize (H11 tc (Rule_getOutputPatternElements r1) (Rule_getOutputPatternElements r2)).
                        specialize (H11 ope H10 H4).
                        destruct H11.
                        destruct H11.
                        destruct H12.
                        destruct H13.
                        exists x.
                        split; auto.
                        split.
                        * unfold evalOutputPatternElementExpr.
                          unfold evalOutputPatternElementExpr in outExpr.
                          rewrite <- H13.
                          auto.       
                        * unfold evalOutputPatternLinkExpr.
                        unfold evalOutputPatternLinkExpr in linkExpr.
                        destruct H14.
                        ** rewrite <- H14.
                           auto.
                        ** rewrite H14 in linkExpr.
                        unfold evalExpr in linkExpr.
                        inversion linkExpr.
                        }
                        destruct H10.
                        apply in_flat_map.
                        exists x.
                        split.
                        * destruct H10.
                          auto.
                        * destruct H10.
                          destruct H11.
                          rewrite H11.
                          rewrite <- H8.
                          rewrite H12.
                          simpl.
                          exact H5.
    ++ contradiction.
  + contradiction.
Qed.

(*********************************************************)
(** * Additivity in OutputPatternLink context            *)
(** * Inductive Definitions                              *)
(*********************************************************)

Inductive Rule_incl_patternElements' {tc: TransformationConfiguration} : list OutputPatternElement -> list OutputPatternElement -> Prop :=
  | incl_e_nil : Rule_incl_patternElements' nil nil
  | incl_e_diff : forall x y xs ys, Rule_incl_patternElements' xs ys 
    -> OutputPatternElement_getName x = OutputPatternElement_getName y 
    -> OutputPatternElement_getElementExpr x = OutputPatternElement_getElementExpr y
    -> (OutputPatternElement_getLinkExpr x = OutputPatternElement_getLinkExpr y \/ 
        OutputPatternElement_getLinkExpr x = (fun _ _ _ _ _ => None))
    -> Rule_incl_patternElements' (x::xs) (y::ys).

Inductive Transformation_incl_rules' {tc: TransformationConfiguration} : list Rule -> list Rule -> Prop :=
  | incl_rules_nil : Transformation_incl_rules' nil nil
  | incl_rules_diff : forall x y xs ys, Transformation_incl_rules' xs ys 
    -> Rule_getName x = Rule_getName y
    -> Rule_getGuardExpr x = Rule_getGuardExpr y  
    -> Rule_getIteratorExpr x = Rule_getIteratorExpr y
    -> Rule_incl_patternElements' (Rule_getOutputPatternElements x) (Rule_getOutputPatternElements y)
    -> Transformation_incl_rules' (x::xs) (y::ys).

Definition Transformation_incl_links' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  (Transformation_incl_rules' (Transformation_getRules t1) (Transformation_getRules t2)).

Lemma tr_incl_equiv:
  forall (tc: TransformationConfiguration) t1 t2,
    Transformation_incl_links' t1 t2 -> Transformation_incl_links t1 t2.
Proof.
intros.
destruct  H.
unfold Transformation_incl_links.
split. 
* auto.
* 
  induction H0.
  ** unfold Transformation_incl_rules. auto.
  ** simpl. repeat split; auto.
     induction H4.
     - unfold Rule_incl_patternElements. auto.
     - simpl. repeat split; auto.
Qed.


Theorem additivity_links' :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_links' t1 t2 -> 
    Model_incl (execute t1 sm) (execute t2 sm)).
Proof.
intros.
specialize (tr_incl_equiv tc t1 t2 H).
specialize (additivity_links tc t1 t2).
auto.
Qed.

