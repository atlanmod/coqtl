Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.Parser.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.properties.AdditivityRule.
Require Import String.
Require Import EqNat.
Require Import List.
Require Import Expressions.
Require Import core.utils.Utils.
Require Import PeanoNat.
Require Import Lia.

Section RuleIrrev.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.

(* ClassMetamodel_eqClass_dec, add to type class of ModelingMetamodel *)
Definition eqb (t1 t2 : TargetModelClass) := true.


Definition output_relevent (r: ConcreteRule) (tp: TargetModelClass) : Prop.
Proof.
destruct (ConcreteRule_getConcreteOutputPattern r) eqn: op.
- exact False.
- specialize (map (ConcreteOutputPatternElement_getOutType) (c::l)).
  intro.
  exact (In tp X).
Qed.

Definition rule_relevent 
  (x y: ConcreteRule) : Prop :=
  ConcreteRule_getName x = ConcreteRule_getName y /\
  forall tp, output_relevent x tp <-> output_relevent y tp .

Inductive Transformation_incl_relevent_rules  : list ConcreteRule -> list ConcreteRule -> Prop :=
  | incl_rules_nil : Transformation_incl_relevent_rules nil nil
  | incl_rules_diff : forall x y xs ys, Transformation_incl_relevent_rules xs ys 
    -> rule_relevent x y
    -> Transformation_incl_relevent_rules (x::xs) (y::ys).


