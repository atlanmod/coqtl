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


Print Transformation_incl_rules''.


(*************************************************************)
(** * Additivity in Rule context                             *)
(*************************************************************)

Definition CocreteTransformation_incl_rules {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc} (t1 t2: ConcreteTransformation) : Prop :=
    subseq (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2).

Lemma CocreteTransformation_incl_rules_imply:
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

Definition Transformation_incl_rules'' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 <= Transformation_getArity t2) /\ 
  subseq (Transformation_getRules t1) (Transformation_getRules t2).


Definition Transformation_incl_rules''' {tc: TransformationConfiguration} (t1 t2: Transformation) : Prop :=
  (Transformation_getArity t1 <= Transformation_getArity t2) /\ 
  forall r: Rule, In r (Transformation_getRules t1) -> In r (Transformation_getRules t2).


Lemma tr_incl_equiv:
  forall (tc: TransformationConfiguration) t1 t2,
    Transformation_incl_rules'' t1 t2 -> Transformation_incl_rules''' t1 t2.
Proof.
intros.
destruct  H.
unfold Transformation_incl_rules'''.
split. 
* auto.
* intro.
  induction H0.
  + intros.
    contradiction.
  + intros.
    simpl in H1.
    simpl.
    destruct H1.
    - left. crush.
    - right. crush.
  + intros.
    simpl.
    right.
    auto.
Qed.

Lemma tuple_length:
 forall {A: Type} (sp: list A) sm n,
  In sp (tuples_up_to_n sm n) -> length sp <= n.
Proof.
intros.
destruct sm eqn: sm_ca.
induction n; crush.
induction n.
- crush.
-
simpl in H.
remember ((map (cons a) (tuples_of_length_n (a :: l) n) ++
        prod_cons l (tuples_of_length_n (a :: l) n))) as l1.
remember (tuples_up_to_n (a :: l) n) as l2.
apply in_app_or in H.
destruct H.
+ admit. 
+ crush.
Admitted.



Lemma allTuples_impl:
 forall (tc: TransformationConfiguration) t1 t2 x sm,
  Transformation_getArity t1 <= Transformation_getArity t2 ->
     In x (allTuples t1 sm) ->  In x (allTuples t2 sm).
Proof.
intros.
destruct t1 as [a1 rs1].
destruct t2 as [a2 rs2].
simpl in H.
unfold allTuples.
unfold allTuples in H0.
simpl.
simpl in H0.
destruct a1, a2.
- auto.
- intros. simpl in H0.
  destruct H0. 
  + apply tuples_up_to_n_incl_length; crush.
    unfold incl.
    intros.
    contradiction.
  + crush.
- crush.
- apply tuples_up_to_n_incl_length.
  Search tuples_up_to_n.
  apply tuples_up_to_n_incl in H0.
  + auto.
  + specialize (tuple_length x (allModelElements sm) (S a1) H0). crush.
Qed.

Lemma additivity_rules_general :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules''' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
simpl.
unfold incl.
intros.
apply in_flat_map in H0. repeat destruct H0. 
apply in_flat_map in H1. repeat destruct H1.
apply filter_In in H1. destruct H1.
destruct H.
apply in_flat_map. exists x.
split.
* specialize (allTuples_impl tc t1 t2 x sm). crush.
* apply in_flat_map.
  specialize (H4 x0 H1).
  exists x0.
  split.
  + apply filter_In.
    split; auto.
  + auto.
Qed.

Theorem additivity_rules :
forall (tc: TransformationConfiguration) (t1 t2: Transformation) (sm: SourceModel),
  (Transformation_incl_rules'' t1 t2 -> 
    incl (allModelElements (execute t1 sm)) (allModelElements (execute t2 sm))).
Proof.
intros.
specialize (tr_incl_equiv tc t1 t2 H).
specialize (additivity_rules_general tc t1 t2).
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
  (CocreteTransformation_incl_rules t1 t2 -> 
    incl (allModelElements (execute (parse t1) sm)) (allModelElements (execute (parse t2) sm))).
Proof.
intros.
specialize (CocreteTransformation_incl_rules_imply (ConcreteTransformation_getConcreteRules t1) (ConcreteTransformation_getConcreteRules t2) H).
intros.
specialize (maxArity_impl t1 t2 H0).
intros.
apply (additivity_rules).
unfold Transformation_incl_rules''.
split.
- auto.
- unfold CocreteTransformation_incl_rules in H.
  simpl.
  apply subseq_parseRule_eq.
  auto.
Qed.
