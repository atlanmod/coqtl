Require Import core.Semantics.
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



(*************************************************************)
(** * Additivity in Rule context                             *)
(*************************************************************)

Definition CocreteTransformation_incl_rules' {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} 
  (t1 t2: ConcreteTransformation) : Prop :=
  (max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules t1))   )) = 
  (max (map (length (A:=SourceModelClass)) (map ConcreteRule_getInTypes (ConcreteTransformation_getConcreteRules t2))   )) /\
    subseq (map parseRule (ConcreteTransformation_getConcreteRules t1))
           (map parseRule (ConcreteTransformation_getConcreteRules t2)).

Definition CocreteTransformation_incl_rules {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} (t1 t2: ConcreteTransformation) : Prop :=
  subseq (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2).

Theorem parse_eq:
  forall (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc)  t1 t2,
    CocreteTransformation_incl_rules' t1 t2 -> 
      Transformation_incl_rules'' (parse t1) (parse t2).
Proof.
intros.
destruct t1 as [crs1].
revert H.
revert t2.
induction crs1.
- intros.
  unfold CocreteTransformation_incl_rules' in H.
  destruct t2 as [crs2].
  destruct crs2 eqn: crs2_ca.
  -- simpl in H.
     unfold Transformation_incl_rules''.
     crush.
  -- simpl in H.
     unfold Transformation_incl_rules''.
     split; simpl; destruct H; auto.
- intro.
  destruct t2 as [crs2].
  induction crs2.
  -- intro.
  unfold CocreteTransformation_incl_rules' in H.
  destruct crs1 eqn: crs1_ca.
  + simpl in H.
     unfold Transformation_incl_rules''.
     crush.
  + simpl in H.
     unfold Transformation_incl_rules''.
     split; simpl; destruct H; auto.
  -- intro. specialize (IHcrs1 (transformation (crs2))).
     unfold Transformation_incl_rules''.
     simpl.
     split.
     + unfold CocreteTransformation_incl_rules' in H.
       simpl in H. destruct H. auto.
     + unfold CocreteTransformation_incl_rules' in H.
       simpl in H.
       crush.
Qed.


Theorem additivity_modeling_rules :
forall (tc: TransformationConfiguration) (mtc: ModelingTransformationConfiguration tc) 
  (t1 t2: ConcreteTransformation) (sm: SourceModel),
  (CocreteTransformation_incl_rules' t1 t2 -> 
    incl (allModelElements (execute (parse t1) sm)) (allModelElements (execute (parse t2) sm))).
Proof.
intros.
specialize (additivity_rules tc (parse t1) (parse t2) sm).
specialize (parse_eq tc mtc t1 t2).
intros.
apply H1.
apply H0.
apply H.
Qed.