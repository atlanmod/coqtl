Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.TransformationConfiguration.

Definition transf_incl {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition targetmodel_incl {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition transf_equiv {tc: TransformationConfiguration} (t1 t2: Transformation) := True.
Definition targetmodel_equiv {tc: TransformationConfiguration} (t1 t2: TargetModel) := True.
Definition sourcemodel_incl {tc: TransformationConfiguration} (t1 t2: SourceModel) := True.


Theorem universality :
forall (tc: TransformationConfiguration) (f: SourceModel -> TargetModel),
  exists (t: Transformation), execute t = f.
Admitted.

Theorem confluence :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  transf_equiv t1 t2 -> targetmodel_equiv (execute t1 sm) (execute t2 sm).
Admitted.

Theorem additivity :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  transf_incl t1 t2 -> targetmodel_incl (execute t1 sm) (execute t2 sm).
Admitted.

Definition monotonicity (tc: TransformationConfiguration) (t: Transformation) :=
    forall (sm1 sm2: SourceModel) (tm1 tm2: TargetModel),
    sourcemodel_incl sm1 sm2 -> targetmodel_incl tm1 tm2.
