Require Import core.Semantics.
Require Import core.Syntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.Parser.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Require Import core.properties.AdditivityRuleExt.
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

Definition ConcreteTransformation_incl_rules {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} (t1 t2: ConcreteTransformation) : Prop :=
    subseq (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2).

Lemma ConcreteTransformation_incl_rules_imply:
 forall {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} rs1 rs2,
  subseq rs1 rs2 ->
    (max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes rs1)   )) <= 
    (max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes rs2)   )) .
Proof.
intros.
induction H; crush.
Qed.

Lemma maxArity_impl:
  forall {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}  t1 t2,
(max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules t1))   )) <= 
(max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules t2))   )) ->
Transformation_getArity (parse t1) <= Transformation_getArity (parse t2).
Proof.
intros.
unfold parse.
simpl.
auto.
Qed.

Lemma subseq_parseRule_eq:
  forall (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc) rs1 rs2,
   subseq rs1 rs2 ->
   subseq (map parseRule rs1) (map parseRule rs2).
Proof.
intros.
induction H.
- simpl. apply s_nil.
- simpl. apply s_true. auto.
- simpl. apply s_false. auto.
Qed.

Theorem additivity_modeling_rules :
forall (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc) 
  (t1 t2: ConcreteTransformation) (sm: SourceModel),
  (ConcreteTransformation_incl_rules t1 t2 -> 
    incl (allModelElements (execute (parse t1) sm)) (allModelElements (execute (parse t2) sm))).
Proof.
intros.
specialize (ConcreteTransformation_incl_rules_imply (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2) H).
intros.
specialize (maxArity_impl t1 t2 H0).
intros.
apply (additivity_rules).
unfold Transformation_incl_rules''.
split.
- auto.
- unfold ConcreteTransformation_incl_rules in H.
  simpl.
  apply subseq_parseRule_eq.
  auto.
Qed.
