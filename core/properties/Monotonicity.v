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
intros.
unfold monotonicity.
unfold TargetModel_incl.
intros.
split.
+ rewrite Forall_forall in H. unfold monotonicity in H. 
  unfold execute. simpl. unfold incl. intros.
  apply in_flat_map in H1. destruct H1. destruct H1.
  apply in_flat_map in H2. destruct H2. destruct H2.

  assert (In x0 (Transformation_getRules tr)).
  { unfold matchPattern in H2. apply filter_In in H2. destruct H2. exact H2. }

  specialize (H x0 H4 sm1 sm2 H0).
  unfold TargetModel_incl in H.
  simpl in H. destruct H. clear H5.
  unfold incl in H. specialize (H a).

  assert (In a (flat_map 
    (instantiatePattern (buildTransformation (Transformation_getArity tr) [x0]) sm1) 
    (allTuples (buildTransformation (Transformation_getArity tr) [x0]) sm1))).
  { clear H.
  apply in_flat_map. exists x.
  split.
  - unfold allTuples in *. crush.
  - unfold instantiatePattern in *.
  apply in_flat_map. exists x0. split.
  -- unfold matchPattern in *. apply filter_In. apply filter_In in H2. crush.
  -- auto.
  }

  specialize (H H5). clear H5.
  apply in_flat_map in H. destruct H. destruct H.
  apply in_flat_map. exists x1.
  split.
  - unfold allTuples in *. crush.
  - unfold instantiatePattern in *.
  apply in_flat_map in H5. destruct H5. destruct H5.
  apply in_flat_map. exists x2. split.
  -- unfold matchPattern in *. apply filter_In. apply filter_In in H5. crush.
  -- auto.

+ rewrite Forall_forall in H.
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



Abort.








(* 

specialize (H5 H6).
apply in_flat_map in H5.
destruct H5.
destruct H5.
apply in_flat_map.
exists x1.
split.
- unfold allTuples in *. crush.
- admit.

unfold applyPattern in H7.
unfold applyRuleOnPattern in H7.
unfold applyIterationOnPattern in H7.
unfold applyElementOnPattern in H7.
unfold matchPattern in H7.
simpl in H7.
destruct (matchRuleOnPattern x0 sm2 x1).
remember ((fun r : Rule =>
           flat_map
             (fun iter : nat =>
              flat_map
                (fun o : OutputPatternElement =>
                 match evalOutputPatternElementExpr sm2 x1 iter o with
                 | return l =>
                     optionListToList
                       (evalOutputPatternLinkExpr sm2 x1 l iter
                          (trace (buildTransformation (Transformation_getArity tr) [x0])
                             sm2) o)
                 | None => nil
                 end) (Rule_getOutputPatternElements r))
             (seq 0 (evalIteratorExpr r sm2 x1)))) as f.

unfold applyPattern.
unfold applyRuleOnPattern.
unfold applyIterationOnPattern.
unfold applyElementOnPattern.
unfold matchPattern.
simpl.
 *)







