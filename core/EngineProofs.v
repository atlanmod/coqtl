(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is an auxilary file for type class for relational transformation
    engine.

 We give here lemmas that can be directly derived from type class [core.Engine]

 **)

 Require Import String.
 Require Import List.
 Require Import Multiset.
 Require Import ListSet.

 Require Import core.Model.
 Require Import core.utils.Utils.
 Require Import core.Engine.

(*********************************************************)
(** * Metatheorems for relational Transformation Engines *)
(*********************************************************)

(** ** maxArity **)

(*Lemma tr_maxArity_in :
  forall (eng: TransformationEngine),
    forall (tr: Transformation) (r: Rule),
      In r (getRules tr) ->
      maxArity tr >= length (getInTypes r).
Proof.
  intros. apply max_list_upperBound. do 2 apply in_map. exact H.
Qed.

Theorem incl_equiv_to_surj:
  forall (eng: TransformationEngine),
    (forall (tr: Transformation) (sm : SourceModel)
       (sp : list SourceModelElement) (tp: list TargetModelElement) (tp1: list TargetModelElement)
       (r : Rule),
        instantiateRuleOnPattern r tr sm sp = Some tp1 ->
        In r (matchPattern tr sm sp) ->
        instantiatePattern tr sm sp = Some tp ->
        incl tp1 tp) <->
    (forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
        instantiatePattern tr sm sp = Some tp ->
        (exists (r : Rule) (tp1 : list TargetModelElement),
            In r (matchPattern tr sm sp) /\
            instantiateRuleOnPattern r tr sm sp = Some tp1 /\
            In te tp1) ->
        In te tp).
Proof.
  split.
  - intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    + pose (H tr sm sp tp x0 x H2 H1 H0).
      apply i in H3.
      assumption.
  - intros.
    unfold incl.
    intros.
    pose (H tr sm sp tp a H2).
    apply i.
    exists r, tp1.
    split. assumption.
    split. assumption.
    assumption.
Qed.

Theorem tr_match_functionality :
  forall (eng: TransformationEngine)
    (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r1: list Rule) (r2: list Rule),
          matchPattern tr sm sp  = r1 -> matchPattern tr sm sp = r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.

Theorem tr_matchPattern_None_tr : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      getRules tr = nil ->
      matchPattern tr sm sp = nil.
Proof.
  intros.
  destruct (matchPattern tr sm sp) eqn:mtch. reflexivity.
  exfalso.
  pose (tr_matchPattern_in tr sm sp r).
  rewrite H in i.
  pose (in_eq r l).
  rewrite <- mtch in i0.
  apply i in i0.
  simpl in i0.
  destruct i0.
  contradiction.
Qed.

  Theorem tr_matchPattern_non_Nil :
    forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
    forall (sp : list SourceModelElement),
      (matchPattern tr sm sp) <> nil <->
      (exists (r: Rule),
        In r (getRules tr) /\
        matchRuleOnPattern r tr sm sp = return true).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (r: Rule), In r (matchPattern tr sm sp)).
      {
        destruct (matchPattern tr sm sp).
        ++ crush.
        ++ exists r.
           crush.
      }
      destruct H0.
      rename x into r.
      exists r.
      apply tr_matchPattern_in. auto.
    + intro.
      destruct H.
      apply tr_matchPattern_in in H.
      destruct (matchPattern tr sm sp).
      ++ inversion H.
      ++ crush.
  Qed.

Theorem tr_instantiatePattern_None_tr : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      getRules tr = nil ->
      (instantiatePattern tr sm sp = None).
Proof.
  intros.
  destruct (instantiatePattern tr sm sp) eqn:dst.
  - apply tr_matchPattern_None_tr with (sm:=sm) (sp:=sp) in H.
    assert (instantiatePattern tr sm sp <> None). { rewrite dst. discriminate. }
    apply tr_instantiatePattern_non_None in H0.
    destruct H0. destruct H0.
    rewrite H in H0.
    destruct H0.
  - reflexivity.
Qed.

Theorem tr_applyPattern_None_tr :
  forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        getRules tr = nil ->
        (applyPattern tr sm sp = None).
Proof.
  intros.
  destruct (applyPattern tr sm sp) eqn:dst.
  - apply tr_matchPattern_None_tr with (sm:=sm) (sp:=sp) in H.
    assert (applyPattern tr sm sp <> None). { rewrite dst. discriminate. }
    apply tr_applyPattern_non_None in H0.
    destruct H0. destruct H0.
    rewrite H in H0.
    destruct H0.
  - reflexivity.
Qed.

Theorem tr_execute_None_tr_elements : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      getRules tr = nil ->
      allModelElements (execute tr sm) = nil.
Proof.
  intros.
  destruct (allModelElements (execute tr sm)) eqn:ame.
  - reflexivity.
  - exfalso.
    pose (tr_execute_in_elements tr sm t0).
    pose (in_eq t0 l).
    rewrite <- ame in i0.
    apply i in i0.
    destruct i0. destruct H0. destruct H0. destruct H1.
    pose (tr_instantiatePattern_in tr sm x t0).
    apply tr_matchPattern_None_tr with (sm:=sm) (sp:=x) in H.
    destruct i0. destruct H3.
    -- exists x0.
       split. assumption. assumption.
    -- destruct H3.
       destruct H3.
       rewrite H in H3.
       contradiction.
Qed.

  Theorem tr_execute_non_Nil_elements :
   forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      (allModelElements (execute tr sm)) <> nil <->
      (exists (te : TargetModelElement) (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (allModelElements sm) /\
          instantiatePattern tr sm sp = Some tp /\
          In te tp).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (te: TargetModelElement), In te (allModelElements (execute tr sm))).
      {
        destruct (allModelElements (execute tr sm)).
        ++ crush.
        ++ exists t.
           crush.
      }
      destruct H0.
      rename x into te.
      exists te.
      apply tr_execute_in_elements. auto.
    + intro.
      destruct H.
      apply tr_execute_in_elements in H.
      destruct (allModelElements (execute tr sm)).
      ++ inversion H.
      ++ crush.
  Qed.


  Theorem tr_execute_non_Nil_links :
   forall eng: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel) ,
      (allModelLinks (execute tr sm)) <> nil <->
      (exists (tl : TargetModelLink) (sp : list SourceModelElement) (tpl : list TargetModelLink),
          incl sp (allModelElements sm) /\
          applyPattern tr sm sp = Some tpl /\
          In tl tpl).
  Proof.
    intros.
    split.
    + intro.
      assert (exists (tl: TargetModelLink), In tl (allModelLinks (execute tr sm))).
      {
        destruct (allModelLinks (execute tr sm)).
        ++ crush.
        ++ exists t.
           crush.
      }
      destruct H0.
      rename x into tl.
      exists tl.
      apply tr_execute_in_links. auto.
    + intro.
      destruct H.
      apply tr_execute_in_links in H.
      destruct (allModelLinks (execute tr sm)).
      ++ inversion H.
      ++ crush.
  Qed.

Theorem tr_execute_None_tr_links : forall t: TransformationEngine,
    forall (tr: Transformation) (sm : SourceModel),
      getRules tr = nil ->
      allModelLinks (execute tr sm) = nil.
Proof.
  intros.
  destruct (allModelLinks (execute tr sm)) eqn:aml.
  - reflexivity.
  - exfalso.
    pose (tr_execute_in_links tr sm t0).
    pose (in_eq t0 l).
    rewrite <- aml in i0.
    apply i in i0.
    destruct i0. destruct H0. destruct H0. destruct H1.
    pose (tr_applyPattern_in tr sm x t0).
    apply tr_matchPattern_None_tr with (sm:=sm) (sp:=x) in H.
    destruct i0. destruct H3.
    -- exists x0.
       split. assumption. assumption.
    -- destruct H3.
       destruct H3.
       rewrite H in H3.
       contradiction.
Qed.

Theorem tr_applyElementOnPattern_None :
   forall eng: TransformationEngine,
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        length sp <> length (getInTypes r) ->
        applyElementOnPattern r ope tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyElementOnPattern r ope tr sm sp i = Some tl).
  { specialize (option_res_dec (applyElementOnPattern r ope tr sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists oper,  In oper (getOutputLinks  (getInTypes r) (getIteratorType r) ope) /\  applyLinkOnPattern r ope oper tr sm sp i <> None).
  { specialize (tr_applyElementOnPattern_non_None tr r sm sp i ope). intros. crush. }
  destruct H2.
  assert ( applyLinkOnPattern r ope x0 tr sm sp i = None).
  { specialize (tr_applyLinkOnPattern_None tr sm r sp i ope x0). intros. crush. }
  crush.
Qed.

Theorem tr_applyIterationOnPattern_None :
   forall eng: TransformationEngine,
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        applyIterationOnPattern r tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyIterationOnPattern r tr sm sp i = Some tl).
  { specialize (option_res_dec (applyIterationOnPattern r tr sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists  ope : OutputPatternElement (getInTypes r) (getIteratorType r),
      In ope (getOutputPattern r) /\ applyElementOnPattern r ope tr sm sp i <> None).
  { specialize (tr_applyIterationOnPattern_non_None tr r sm sp i). crush. }
  destruct H2.
  destruct H2.
  assert ( applyElementOnPattern r x0 tr sm sp i = None).
  { specialize (tr_applyElementOnPattern_None eng tr sm r sp i x0). intros. crush. }
  crush.
Qed.

Theorem tr_applyRuleOnPattern_None :
   forall eng: TransformationEngine,
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (getInTypes r) ->
        applyRuleOnPattern r tr sm sp = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tl: list TargetModelLink), applyRuleOnPattern r tr sm sp = Some tl).
  { specialize (option_res_dec (applyRuleOnPattern r tr sm)). intros.
    specialize (H1 sp H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists (i: nat), i < length (evalIterator r sm sp) /\ applyIterationOnPattern r tr sm sp i <> None).
  { specialize (tr_applyRuleOnPattern_non_None tr r sm sp). crush. }
  destruct H2.
  destruct H2.
  assert (applyIterationOnPattern r tr sm sp x0 = None).
  { specialize (tr_applyIterationOnPattern_None eng tr sm r sp x0). crush. }
  crush.
Qed.

Theorem tr_instantiateIterationOnPattern_None :
   forall eng: TransformationEngine,
     forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        instantiateIterationOnPattern r sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tp: list TargetModelElement), instantiateIterationOnPattern r sm sp i = Some tp).
  { specialize (option_res_dec (instantiateIterationOnPattern r sm sp)). intros.
    specialize (H1 i H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists  ope : OutputPatternElement (getInTypes r) (getIteratorType r),
      In ope (getOutputPattern r) /\ instantiateElementOnPattern r ope sm sp i <> None).
  { specialize (tr_instantiateIterationOnPattern_non_None r sm sp i). crush. }
  destruct H2.
  destruct H2.
  assert ( instantiateElementOnPattern r x0 sm sp i = None).
  { specialize (tr_instantiateElementOnPattern_None sm r sp i x0). intros. crush. }
  crush.
Qed.

Theorem tr_instantiateRuleOnPattern_None :
  forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      length sp <> length (getInTypes r) ->
      instantiateRuleOnPattern r tr sm sp = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  assert (exists (tp: list TargetModelElement), instantiateRuleOnPattern r tr sm sp = Some tp).
  { specialize (option_res_dec (instantiateRuleOnPattern r tr sm)). intros.
    specialize (H1 sp H0). destruct H1. exists x. crush. }
  destruct H1.
  assert (exists (i: nat), i < length (evalIterator r sm sp) /\ instantiateIterationOnPattern r sm sp i <> None).
  { specialize (tr_instantiateRuleOnPattern_non_None tr r sm sp). crush. }
  destruct H2.
  destruct H2.
  assert (instantiateIterationOnPattern r sm sp x0 = None).
  { specialize (tr_instantiateIterationOnPattern_None eng sm r sp x0). crush. }
  crush.
Qed.

Theorem tr_instantiateIterationOnPattern_None_iterator :
 forall eng: TransformationEngine,
  forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      instantiateIterationOnPattern r sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_instantiateIterationOnPattern_non_None r sm sp i).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_instantiateElementOnPattern_None_iterator sm r sp x H).
  crush.
Qed.

Theorem tr_applyElementOnPattern_None_iterator :
  forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      applyElementOnPattern r ope tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_applyElementOnPattern_non_None tr r sm sp i ope).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_applyLinkOnPattern_None_iterator tr sm r sp).
  intros.
  specialize (H4 i ope x H).
  crush.
Qed.

Theorem tr_applyIterationOnPattern_None_iterator :
   forall eng: TransformationEngine,
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      applyIterationOnPattern r tr sm sp i = None.
Proof.
  intros. apply None_is_not_non_None. intro H0.
  specialize (tr_applyIterationOnPattern_non_None tr r sm sp i).
  intros.
  destruct H1.
  specialize (H1 H0).
  destruct H1. destruct H1.
  specialize (tr_applyElementOnPattern_None_iterator eng tr sm r sp i x H).
  crush.
Qed.
*)