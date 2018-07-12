Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.

Require Import HSM.
Require Import FSM.


Definition isNone (A: Type) (e : option A) : bool :=
 match e with
  | None => true
  | Some a => false
 end.

Definition HSM2FSMConcrete :=
  transformation HSM2FSM from HSMMetamodel to FSMMetamodel
    with m as HSMModel := [

       rule SM2SM
         from
           element sm1 class StateMachineEClass from HSMMetamodel
             when true
         to
          [
           output "sm2"
             element sm2 class FStateMachineEClass from FSMMetamodel :=
               BuildFStateMachine (getStateMachineName sm1)
             links
               nil
          ]
        ;

       rule RS2RS
         from
           element rs1 class RegularStateEClass from HSMMetamodel
             when true
         to
          [
           output "rs2"
             element rs2 class FRegularStateEClass from FSMMetamodel :=
               BuildFRegularState (getRegularStateName rs1)
             links
               [
                 reference FRegularStateStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (getRegularStateStateMachineOnLinks rs1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFRegularStateStateMachine rs2 fsm_sm 
               ]
          ]
        ;

       rule IS2IS
         from
           element is1 class InitialStateEClass from HSMMetamodel
             when (isNone CompositeState (getInitialStateCompositeStateOnLinks is1 m))
         to
          [
           output "is2"
             element is2 class FInitialStateEClass from FSMMetamodel :=
               BuildFInitialState (getInitialStateName is1)
             links
               [
                 reference FInitialStateStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (getInitialStateStateMachineOnLinks is1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFInitialStateStateMachine is2 fsm_sm 
               ]
          ]
        ;

       rule IS2RS
         from
           element is1 class InitialStateEClass from HSMMetamodel
             when (negb (isNone CompositeState (getInitialStateCompositeStateOnLinks is1 m)))
         to
          [
           output "rs2"
             element rs2 class FRegularStateEClass from FSMMetamodel :=
               BuildFRegularState (getInitialStateName is1)
             links
               [
                 reference FRegularStateStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (getInitialStateStateMachineOnLinks is1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFRegularStateStateMachine rs2 fsm_sm 
               ]
          ]

  ].

(* Unset Printing Notations.*)
(* Print Class2Relational. *)
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition HSM2FSM := parseTransformation HSM2FSMConcrete.



