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

Definition transf_incl {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition sourcemodel_incl {tc: TransformationConfiguration} (t1 t2: SourceModel) := True.
Definition targetmodel_incl {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition targetmodel_equiv {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.

Definition Rule_eqdec: forall {tc: TransformationConfiguration}  (x y:Rule), {x = y} + {x <> y}.
Admitted.

(* Compute elementAt 3 (indexedElements 1 (3::4::5::nil)). *)

Theorem universality_elements :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  exists (t: Transformation), 
  forall (sm: SourceModel), allModelElements (execute t sm) = allModelElements (f sm).
Proof.
  intros.
  exists (buildTransformation 0 
    ((buildRule "rule"%string 
     (fun sm sp => match sp with nil => Some true | _ => Some false end)
     (fun sm sp => Some (length (allModelElements (f sm))))
      (buildOutputPatternElement "out"%string 
      (fun i sm sp => nth_error (allModelElements (f sm)) i)
      (fun tls i sm sp te => None) 
      :: nil))
     ::nil)).
  intros.
  unfold execute. 
  unfold instantiatePattern. 
  unfold instantiateRuleOnPattern. 
  unfold instantiateIterationOnPattern. 
  unfold evalIteratorExpr. 
  simpl.
  destruct (f sm).
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
