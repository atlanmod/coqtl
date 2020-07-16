(**

 CoqTL user theorem: RegularState_instantiate

 Def: all regular state in the source model will be instantiated

 Proved with engine specification

 **)

Require Import String.
Require Import Coq.Logic.Eqdep_dec.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.


Require Import examples.HSM2FSM.HSM.
Require Import examples.HSM2FSM.HSM2FSM.

Theorem RegularState_instantiate_spec :
  forall (cm : HSMModel) (s: AbstractState),
        (AbstractState_instanceOfEClass RegularStateEClass s) = true ->
    exists (t: AbstractState) tp,
      instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some tp /\
      In (HSMMetamodel_toEObject t) tp.
Proof.
  intros.
  eexists.
  apply tr_instantiatePattern_in.
  do 2 eexists.
  repeat split.
  - apply tr_matchPattern_in.
    split.
    + right. left. reflexivity.
    + (* rewrite tr_matchRuleOnPattern. *)
      unfold matchRuleOnPattern'. unfold matchRuleOnPattern. unfold evalGuard.
      unfold Expressions.evalFunction. simpl. rewrite H. auto.
  - (* rewrite tr_instantiateRuleOnPattern. *)
    unfold instantiateRuleOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateIterationOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    unfold instantiateElementOnPattern. unfold matchRuleOnPattern. unfold evalGuard.
    unfold Expressions.evalFunction. simpl Expressions.evalFunctionFix. rewrite H.
    simpl. reflexivity.
  - left. reflexivity.
Qed.