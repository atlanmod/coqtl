(**

 CoqTL user theorem: All_sm_instantiate

 Def: all state machine in the source model will create state machine in the target model

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

Theorem All_sm_instantiate_impl :
  forall (cm : HSMModel) (s : StateMachine),
  exists (t : StateMachine),
    instantiatePattern HSM2FSM cm [HSMMetamodel_toEObject s] = Some [HSMMetamodel_toEObject t].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.