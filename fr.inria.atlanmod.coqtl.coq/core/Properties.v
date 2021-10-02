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

Definition transf_incl {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition sourcemodel_incl {tc: TransformationConfiguration} (t1 t2: SourceModel) := True.
Definition targetmodel_incl {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition targetmodel_equiv {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.

Definition Rule_eqdec: forall {tc: TransformationConfiguration}  (x y:Rule), {x = y} + {x <> y}.
Admitted.

(* Compute elementAt 3 (indexedElements 1 (3::4::5::nil)). *)

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
  apply (H sm) in H0.
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


Theorem confluence :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (forall (r: Rule), count_occ Rule_eqdec (Transformation_getRules t1) r = count_occ Rule_eqdec (Transformation_getRules t2) r)
  -> targetmodel_equiv (execute t1 sm) (execute t2 sm).
Admitted.

Theorem additivity :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  transf_incl t1 t2 -> targetmodel_incl (execute t1 sm) (execute t2 sm).
Admitted.

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
  forall (sm1 sm2: SourceModel),
  sourcemodel_incl sm1 sm2 -> targetmodel_incl (execute t sm1) (execute t sm2).
