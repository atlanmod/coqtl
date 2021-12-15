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
  rewrite Forall_forall in mono. unfold monotonicity in mono. 
  unfold execute. simpl. unfold incl. intros e in_sm1.
  apply in_flat_map in in_sm1. 
  destruct in_sm1 as [sp temp]. destruct temp as [in_sp in_e].
  apply in_flat_map in in_e. 
  destruct in_e as [r temp]. destruct temp as [in_r in_e].

  assert (In r (Transformation_getRules tr)) as in_tr.
  { unfold matchPattern in in_r. apply filter_In in in_r. crush. }

  specialize (mono r in_tr sm1 sm2 sm_incl).
  unfold TargetModel_incl in mono.
  simpl in mono. destruct mono as [elem_incl link_incl]. clear link_incl.
  unfold incl in elem_incl. specialize (elem_incl e).

  remember (buildTransformation (Transformation_getArity tr) [r]) as tr_singleton.
  assert (In e (flat_map (instantiatePattern tr_singleton sm1)
               (allTuples tr_singleton sm1))) as in_e_single.
  { clear elem_incl.
    apply in_flat_map. exists sp. split.
    - unfold allTuples in *. crush.
    - unfold instantiatePattern in *.
      apply in_flat_map. exists r. split.
      -- unfold matchPattern in *. 
        apply filter_In. apply filter_In in in_r. crush.
      -- auto.
  }

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
(* rewrite Forall_forall in H.
  unfold monotonicity in H.

  unfold execute.
  simpl.
  unfold incl.
  intros.

  apply in_flat_map in H1.
  destruct H1. destruct H1.
  apply in_flat_map in H2.
  destruct H2. destruct H2.

  assert (In x0 (Transformation_getRules tr)).
  { unfold matchPattern in H2. apply filter_In in H2. crush. }

  specialize (H x0 H4 sm1 sm2 H0).

  unfold TargetModel_incl in H.
  unfold incl in H.
  destruct H.
  specialize (H5 a).
  clear H.

assert (In a
       (allModelLinks
          (execute (buildTransformation (Transformation_getArity tr) [x0]) sm1))).
{ 

intros.
unfold execute.
simpl.
apply in_flat_map.
exists x.
split.
- unfold allTuples in *. crush.
- apply in_flat_map.
exists x0.
split.
unfold matchPattern in *.
apply filter_In in H2.
apply filter_In.
crush.
apply in_flat_map.
apply in_flat_map in H3.
destruct H3. 
destruct H.
exists x1. crush.
apply in_flat_map.
apply in_flat_map in H3.
destruct H3. destruct H3.
exists x2. crush. 
unfold applyElementOnPattern in *.
destruct (evalOutputPatternElementExpr sm1 x x1 x2). 
+ admit.  (* <-- trace *)
+ auto.

}

*)

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









