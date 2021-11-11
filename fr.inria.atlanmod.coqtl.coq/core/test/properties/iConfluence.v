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

Context (tc: TransformationConfiguration).

(* Set semantics: we think that the list of rules represents a set (we don't allow two rules to have the same name)*)
Definition Transformation_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := 
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  forall (r:Rule), In r (Transformation_getRules t1) <-> In r (Transformation_getRules t2).

Definition TargetModel_equiv {tc: TransformationConfiguration} (m1 m2: TargetModel) :=
  forall (e: TargetModelElement) (l: TargetModelLink),
   (In e (allModelElements m1) <-> In e (allModelElements m2)) /\
    (In l (allModelLinks m1) <-> In l (allModelLinks m2)).


(* Theorem trace_eq :
forall  t1 t2 sm,
  Transformation_equiv t1 t2 -> 
   (forall tl, In tl (trace t1 sm) <-> In tl (trace t2 sm)) /\
   length (trace t1 sm) = length (trace t2 sm).
Proof.
Admitted. *)


Theorem filter_length_eq :
forall {A:Type} t1 t2 f,
   (forall e:A, In e t1 <-> In e t2) ->
     length t1 = length t2 ->
     length (filter f t1) = length (filter f t2).
Proof.
intros.
revert H.
revert H0.
revert t2.
induction t1.
- intros. 
  destruct t2 eqn: t2_ca.
  + auto.
  + specialize (H a).
    destruct H.
    simpl in H1.
    crush.
- intros.
  induction t2.
  + admit.
  + clear IHt2.
Abort.



Theorem filter_eq :
forall {A:Type} t1 t2 f,
   (forall e:A, In e t1 <-> In e t2) ->
     forall e:A, In e (filter f t1) <-> In e (filter f t2).
Proof.
intros.
revert H.
revert t2.
induction t1.
- intros. specialize (H e).
  split.
  + intro. simpl in H0. inversion H0.
  + destruct t2.
    ++ auto.
    ++ intro.
      apply filter_In in H0.
      destruct H0.
      destruct H.
      specialize ((H2 H0)).
      simpl in H2.
      inversion H2.
- intros.
  induction t2.
  + split.
    ++ intro. specialize (H e).
      apply filter_In in H0.
      destruct H0.
      destruct H.
      specialize ((H H0)).
      simpl in H.
      inversion H.
    ++ intro. specialize (H e).
      apply filter_In in H0.
      destruct H0.
      simpl in H0.
      inversion H0.
  + clear IHt2.
    split.
    ++ intro.
       apply filter_In.
       apply filter_In in H0.
       split.
       * destruct H0.
        simpl in H0.
        destruct H0.
        ** rewrite <- H0.
          specialize (H a).
          apply H.
          simpl.
          left.
          auto.
        ** specialize (H e).
          destruct H.
          apply H.
          simpl.
          right.
          exact H0.
       * destruct H0. auto.
    ++ intro.
       apply filter_In.
       apply filter_In in H0.
       split.
       * destruct H0.
        simpl in H0.
        destruct H0.
        ** rewrite <- H0.
          specialize (H a0).
          apply H.
          simpl.
          left.
          auto.
        ** specialize (H e).
          destruct H.
          apply H2.
          simpl.
          right.
          exact H0.
       * destruct H0. auto.
Qed. 

(* Theorem length_eq :
forall  {A:Type} (l1 l2: list A),
  (forall e, In e l1 <-> In e l2) ->
    length l1 = length l2.
Proof. *)
(* intros.
revert H.
revert l2.
induction l1.
- intros.
  destruct l2 eqn:l2_ca.
  + auto.
  + specialize (H a).
  destruct H.
  simpl in H0.
  destruct H0.
  left. auto.
- intros.
induction l2.
+ specialize (H a).
  destruct H.
  simpl in H.
  crush.
+ simpl.
  apply eq_S.
  apply IHl1.
  intro.
  specialize (H e).
  split.
  * intro.
  admit.
  * intro.
  destruct H.
  simpl in H1.
  assert (a = e \/ In e l1). { admit. }
  destruct H2.
  ** admit. 
Abort. *)


Theorem filter_eq_length :
forall  {A:Type} (l1 l2: list A),
  (forall e, In e l1 <-> In e l2) ->
    length l1 = length l2 ->
    length l1 = 1 -> 
      nth_error l1 0 = nth_error l2 0.
Proof.
intros.
rewrite H1 in H0. symmetry in H0.
induction l1; induction l2.
- inversion H0.
- inversion H1.
- rewrite <- H0 in H1. inversion H1.
- simpl.
assert (l1 = nil). { simpl in H0. destruct l1. auto. simpl in H0. crush. }
assert (l2 = nil). { simpl in H1. destruct l2. auto. simpl in H1. crush. }
rewrite H2 in H.
rewrite H3 in H.
simpl in H.
specialize (H a).
crush.
Qed.



(* TODO  lack uniqueness in generated tracelink *)
Lemma resolveIter_eq :
forall  t1 t2 sm,
   Transformation_equiv t1 t2 ->
   resolveIter (trace t1 sm) = resolveIter (trace t2 sm).
Proof.
intros.
unfold resolveIter.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.
apply functional_extensionality. intro.

remember ((fun tl0 : TraceLink =>
        (iSemantics.list_beq SourceModelElement SourceElement_eqb
           (TraceLink_getSourcePattern tl0) x1 && (TraceLink_getIterator tl0 =? x2) &&
         (TraceLink_getName tl0 =? x0)%string)%bool)) as tr_filter.

remember ((filter tr_filter (trace t1 sm))) as l1.
remember ((filter tr_filter (trace t2 sm))) as l2.


Admitted.
(* rewrite <- Heql1 in H0. rewrite <- Heql2 in H0.
specialize (@length_eq TraceLink l1 l2 H0).
intro.

destruct (Datatypes.length l1) eqn: l1_length.
+ rewrite <- H1. auto.
+ rewrite <- H1.
  destruct n.
  - specialize (@filter_eq_length TraceLink l1 l2 H0 l1_length).
  intro.
  rewrite H2.
  auto.
  - auto.
Qed. *)








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
{ admit. }
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
{ admit. }
destruct (evalOutputPatternElementExpr sm x x1 x2) eqn: eval_ope_ca.
*** rewrite <- H7 in H6.
    auto.
*** auto.
Admitted.
