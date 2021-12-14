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
  incl (allModelElements m1) (allModelElements m2).
(* /\ incl (allModelLinks m1) (allModelLinks m2). *)

Definition TargetModel_incl {tc: TransformationConfiguration}  (m1 m2: TargetModel) : Prop := 
  incl (allModelElements m1) (allModelElements m2).
(* /\ incl (allModelLinks m1) (allModelLinks m2). *)

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  SourceModel_incl sm1 sm2 -> TargetModel_incl (execute t sm1) (execute t sm2).


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


Theorem monotonicity_lifting :
  forall (tc: TransformationConfiguration) 
  (tr: Transformation),
    Forall 
      (fun r => monotonicity tc (buildTransformation (Transformation_getArity tr) [ r ]))
      (Transformation_getRules tr) 
        -> monotonicity tc tr.
Proof.
intros.
destruct tr.
induction l.
- unfold monotonicity .
  intros.
  unfold TargetModel_incl.
  unfold incl.
  intros.
  simpl in H1.
  apply in_flat_map in H1.
  destruct H1. destruct H1.
  unfold instantiatePattern in H2.
  simpl in H2.
  inversion H2.
- simpl in H.
  simpl in IHl.
  specialize (Forall_inv H).
  intro. simpl in H0.
  specialize (Forall_inv_tail H).
  intro. simpl in H1.
  specialize (IHl H1).
  clear H1.
  unfold monotonicity.
  intros.
  unfold TargetModel_incl.
  unfold execute.
  simpl.
  unfold incl.
  intros.

  apply in_flat_map in H2.
  destruct H2. destruct H2.

  unfold monotonicity in IHl.
  unfold TargetModel_incl in IHl.
  unfold incl in IHl.
  specialize (IHl sm1 sm2 H1 a0).

  unfold monotonicity in H0.
  unfold TargetModel_incl in H0.
  unfold incl in H0.
  specialize (H0 sm1 sm2 H1 a0).

  specialize (instantiatePattern_distributive tc a0 x sm1 n a l).
  intro.
  destruct H4.
  specialize (H4 H3).
  destruct H4.
  + unfold execute in H0.
    simpl in H0.
    assert (In a0
    (flat_map (instantiatePattern (buildTransformation n [a]) sm1)
      (allTuples (buildTransformation n [a]) sm1))).
    {  apply in_flat_map. exists x. crush. }
    specialize (H0 H6).
    apply in_flat_map.
    apply in_flat_map in H0.
    destruct H0. destruct H0.
    exists x0. split.
    ++ unfold allTuples. simpl.
    unfold allTuples in H0. simpl in H0. auto.
    ++ specialize (instantiatePattern_distributive tc a0 x0 sm2 n a l).
    intro.
    destruct H8.
    apply H9.
    left. auto.
  + clear H0.
  unfold execute in IHl.
    simpl in IHl.
    assert (In a0
    (flat_map (instantiatePattern (buildTransformation n l) sm1)
      (allTuples (buildTransformation n l) sm1))).
    { apply in_flat_map. exists x. crush. }
    specialize (IHl H0).
    apply in_flat_map.
    apply in_flat_map in IHl.
    destruct IHl. destruct H6.
    exists x0. split.
    ++ unfold allTuples. simpl.
    unfold allTuples in H6. simpl in H6. auto.
    ++ specialize (instantiatePattern_distributive tc a0 x0 sm2 n a l).
    intro.
    destruct H8.
    apply H9.
    right. auto.
Qed.










