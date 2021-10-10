Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.Parser.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.


(*************************************************************)
(** * Additivity in Rule context                             *)
(*************************************************************)

Definition CocreteTransformation_incl_rules {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} (t1 t2: ConcreteTransformation) : Prop :=
  subseq (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2).

Theorem additivity_modeling_rules :
forall (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc) 
  (t1 t2: ConcreteTransformation) (sm: SourceModel),
  (CocreteTransformation_incl_rules t1 t2 -> 
    incl (allModelElements (execute (parse t1) sm)) (allModelElements (execute (parse t2) sm))).
Proof.
Admitted.