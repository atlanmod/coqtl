Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.
Require Import List.

Definition transf_incl {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition sourcemodel_incl {tc: TransformationConfiguration} (t1 t2: SourceModel) := True.
Definition targetmodel_incl {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition targetmodel_equiv {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.

Definition Rule_eqdec: forall {tc: TransformationConfiguration}  (x y:Rule), {x = y} + {x <> y}.
Admitted.

Theorem universality :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  exists (t: Transformation), execute t = f.
Admitted.

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
