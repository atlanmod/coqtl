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

Theorem All_sm_match_impl :
  forall (cm : HSMModel) (s : StateMachine),
  exists (r : Rule HSMMetamodel HSMMetamodel),
    matchPattern HSM2FSM cm [HSMMetamodel_toEObject s] = [r].
Proof.
  intros.
  eexists _.
  reflexivity.
Qed.