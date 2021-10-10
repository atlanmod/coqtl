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
(** * Additivity in OutputPatternElement context             *)
(*************************************************************)

Definition Rule_incl_modeling_elements {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} 
  (x y: ConcreteRule) : Prop :=
  ConcreteRule_getName x = ConcreteRule_getName y
  /\ ConcreteRule_getInTypes x = ConcreteRule_getInTypes y
  /\ ConcreteRule_getGuard x = ConcreteRule_getGuard y  
  /\ ConcreteRule_getIteratedList x = ConcreteRule_getIteratedList y
  /\ subseq (ConcreteRule_getConcreteOutputPattern x) (ConcreteRule_getConcreteOutputPattern y).

Inductive Transformation_incl_modeling_rules {tc: TransformationConfiguration}  : list Rule -> list Rule -> Prop :=
  | incl_rules_nil : Transformation_incl_modeling_rules nil nil
  | incl_rules_diff : forall x y xs ys, Transformation_incl_modeling_rules xs ys 
    -> Rule_incl_modeling_elements x y
    -> Transformation_incl_modeling_rules (x::xs) (y::ys).

Definition Transformation_incl_modeling_elements {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 = Transformation_getArity t2) /\ 
  Transformation_incl_rules' (Transformation_getRules t1) (Transformation_getRules t2). 

Theorem additivity_modeling_elements :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_elements'' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
Admitted.