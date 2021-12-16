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
(** * Monotonicity                                           *)
(*************************************************************)

Definition SourceModel_incl {tc: TransformationConfiguration}  (m1 m2: SourceModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2)
/\ incl (allModelLinks m1) (allModelLinks m2). 

Definition TargetModel_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2)
/\ incl (allModelLinks m1) (allModelLinks m2). 

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  SourceModel_incl sm1 sm2 -> TargetModel_incl (execute t sm1) (execute t sm2).

Theorem monotonicity_lifting :
  forall (tc: TransformationConfiguration) 
  (tr: Transformation),
    Forall 
      (fun r => monotonicity tc (buildTransformation (Transformation_getArity tr) [ r ]))
      (Transformation_getRules tr) 
        -> monotonicity tc tr.
Proof.
intros tc tr mono. unfold monotonicity. unfold TargetModel_incl.
intros sm1 sm2 sm_incl. split.
+ (* mono_lift_elem *)

  (* prove In e (exeucte tr sm1) *)
  rewrite Forall_forall in mono. unfold monotonicity in mono. 
  unfold execute. simpl. unfold incl. intros e in_sm1.
  apply in_flat_map in in_sm1. 
  destruct in_sm1 as [sp temp]. destruct temp as [in_sp in_e].
  apply in_flat_map in in_e. 
  destruct in_e as [r temp]. destruct temp as [in_r in_e].

  (* prove In e (exeucte tr sm1) -> In e (exeucte tr_singleton sm1) *)
  remember (buildTransformation (Transformation_getArity tr) [r]) as tr_singleton.
  assert (In e (flat_map (instantiatePattern tr_singleton sm1)
               (allTuples tr_singleton sm1))) as in_e_single.
  { 
    apply in_flat_map. exists sp. split.
    - unfold allTuples in *. crush.
    - unfold instantiatePattern in *.
      apply in_flat_map. exists r. split.
      -- unfold matchPattern in *. 
        apply filter_In. apply filter_In in in_r. crush.
      -- auto.
  }

  (* by mono In e (exeucte tr_singleton sm1) -> 
             In e (exeucte tr_singleton sm2) *)
  assert (In r (Transformation_getRules tr)) as in_tr.
  { unfold matchPattern in in_r. apply filter_In in in_r. crush. }
  specialize (mono r in_tr sm1 sm2 sm_incl).
  unfold TargetModel_incl in mono.
  simpl in mono. destruct mono as [elem_incl link_incl]. clear link_incl.
  unfold incl in elem_incl. specialize (elem_incl e).

  (* prove In e (exeucte tr_singleton sm2) -> In e (exeucte tr sm2) *)
  rewrite <- Heqtr_singleton in elem_incl.
  specialize (elem_incl in_e_single). clear in_e_single.
  apply in_flat_map in elem_incl.
  destruct elem_incl as [sp2 temp]. destruct temp as [in_sp2 in_e_sm2].
  apply in_flat_map. exists sp2.
  split.
  - unfold allTuples in *. crush.
  - unfold instantiatePattern in *.
    apply in_flat_map in in_e_sm2. 
    destruct in_e_sm2 as [r2 temp]. destruct temp as [in_r2 in_e_sm2].
    apply in_flat_map. exists r2. split.
    -- unfold matchPattern in *. 
       apply filter_In. apply filter_In in in_r2. crush.
    -- auto.

+ (* mono_lift_links *)

  (* prove In l (exeucte tr sm1) *)
  rewrite Forall_forall in mono. unfold monotonicity in mono. 
  unfold execute. simpl. unfold incl. intros l in_sm1.
  apply in_flat_map in in_sm1. 
  destruct in_sm1 as [sp temp]. destruct temp as [in_sp in_l_sm1].
  apply in_flat_map in in_l_sm1. 
  destruct in_l_sm1 as [r temp]. destruct temp as [in_r in_l_sm1].

  (* prove In l (exeucte tr sm1) -> In l (exeucte tr_singleton sm1) *)
  remember (buildTransformation (Transformation_getArity tr) [r]) as tr_singleton.
  assert (In l (flat_map (applyPattern tr_singleton sm1)
               (allTuples tr_singleton sm1))) as in_l_single.
  { apply in_flat_map. exists sp. split.
    - unfold allTuples in *. crush.
    - unfold applyPattern in *.
      apply in_flat_map. exists r. split.
      -- unfold matchPattern in *. 
         apply filter_In. apply filter_In in in_r. crush.
      -- apply in_flat_map in in_l_sm1. 
         destruct in_l_sm1 as [it temp]. destruct temp as [it_in in_l_sm1].
         apply in_flat_map. exists it. split.
         + auto.
         + apply in_flat_map in in_l_sm1.
           destruct in_l_sm1 as [ope temp]. destruct temp as [ope_in in_l_sm1].
           apply in_flat_map. exists ope. split.
           ++ auto.
           ++ unfold applyElementOnPattern in *.
              destruct (evalOutputPatternElementExpr sm1 sp it). 
(* not hold: 
  (evalOutputPatternLinkExpr sm1 sp t it (trace tr sm1) ope) -> 
  (evalOutputPatternLinkExpr sm1 sp t it (trace tr_singleton sm1) ope) *)
Abort.









(* sth. useful on instantiatePattern *)
Lemma instantiatePattern_distributive:
forall (tc: TransformationConfiguration),
  forall a0 sp sm1 n a l,
In a0 (instantiatePattern (buildTransformation n (a :: l)) sm1 sp) <->
In a0 (instantiatePattern (buildTransformation n [a]) sm1 sp) \/
In a0 (instantiatePattern (buildTransformation n l) sm1 sp).
Proof.
intros.
split.
+ intro.
  unfold instantiatePattern in H.
  unfold instantiateRuleOnPattern  in H.
  unfold instantiateIterationOnPattern in H.
  unfold matchPattern in H.
  simpl in H.
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  unfold instantiateIterationOnPattern.
  unfold matchPattern.
  simpl. 
  remember ((fun r : Rule =>
  flat_map
    (fun iter : nat =>
     flat_map
       (fun o : OutputPatternElement =>
        optionToList (instantiateElementOnPattern o sm1 sp iter))
       (Rule_getOutputPatternElements r))
    (seq 0 (evalIteratorExpr r sm1 sp)))) as f.
  remember (filter (fun r : Rule => matchRuleOnPattern r sm1 sp) l) as l1.
  destruct (matchRuleOnPattern a sm1 sp) eqn: ca.
  - apply in_flat_map in H.
    destruct H. destruct H.
    destruct H.
    -- rewrite <- H in H0. left. apply in_flat_map. exists x. crush.
    -- right. apply in_flat_map. exists x. crush.
  - right. auto.
+ intro.
unfold instantiatePattern.
unfold instantiateRuleOnPattern.
unfold instantiateIterationOnPattern.
unfold matchPattern.
simpl. 
remember ((fun r : Rule =>
flat_map
  (fun iter : nat =>
   flat_map
     (fun o : OutputPatternElement =>
      optionToList (instantiateElementOnPattern o sm1 sp iter))
     (Rule_getOutputPatternElements r))
  (seq 0 (evalIteratorExpr r sm1 sp)))) as f.
remember (filter (fun r : Rule => matchRuleOnPattern r sm1 sp) l) as l1.
destruct (matchRuleOnPattern a sm1 sp) eqn: ca.
++ destruct H.
- unfold instantiatePattern in H.
unfold instantiateRuleOnPattern in H.
unfold instantiateIterationOnPattern in H.
unfold matchPattern in H.
simpl in H.
rewrite ca in H.
rewrite <- Heqf in H.
apply in_flat_map in H. destruct H.
apply in_flat_map. exists x. split. crush. crush. 
- unfold instantiatePattern in H.
unfold instantiateRuleOnPattern in H.
unfold instantiateIterationOnPattern in H.
unfold matchPattern in H.
simpl in H.
rewrite <- Heqf in H.
apply in_flat_map in H.
destruct H.
apply in_flat_map.
exists x. split; crush.
++ destruct H. 
unfold instantiatePattern in H.
unfold instantiateRuleOnPattern in H.
unfold instantiateIterationOnPattern in H.
unfold matchPattern in H.
simpl in H.
rewrite ca in H.
rewrite <- Heqf in H.
simpl in H. inversion H.
unfold instantiatePattern in H.
unfold instantiateRuleOnPattern in H.
unfold instantiateIterationOnPattern in H.
unfold matchPattern in H.
simpl in H.
rewrite <- Heqf in H.
apply in_flat_map in H.
destruct H.
apply in_flat_map.
exists x. split; crush.
Qed.









