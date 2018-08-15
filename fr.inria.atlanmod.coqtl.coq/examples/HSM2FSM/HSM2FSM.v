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

Definition isComposite (e : option AbstractState) (m : HSMModel) : bool :=
 match e with
  | None => false
  | Some a => negb (isNone CompositeState (AbstractState_downcastCompositeState a m))
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
               BuildFStateMachine (StateMachine_getName sm1) (StateMachine_getStateMachineID sm1)
             links
               nil
          ]
        ;

      (* AbstractState to FAbstractState, need to be explicit *)
       rule AS2AS
         from
           element as1 class AbstractStateEClass from HSMMetamodel
             when true
         to
          [
           output "as2"
             element as2 class FAbstractStateEClass from FSMMetamodel :=
               BuildFAbstractState (AbstractState_getName as1) (AbstractState_getAbstractStateID as1)
             links
               [
                 reference FAbstractStateStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (AbstractState_getStateMachine as1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFAbstractStateStateMachine as2 fsm_sm 
               ]
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
               let hsm_as := (RegularState_getAbstractState rs1) in
                let fsm_as := (BuildFAbstractState (AbstractState_getName hsm_as) (AbstractState_getAbstractStateID hsm_as)) in
                  BuildFRegularState fsm_as (RegularState_getRegularStateID rs1)
             links
               nil
          ]
      ;

      rule IS2IS
         from
           element is1 class InitialStateEClass from HSMMetamodel
             when (isNone CompositeState (AbstractState_getCompositeState (InitialState_getAbstractState is1) m))
         to
          [
           output "is2"
             element is2 class FInitialStateEClass from FSMMetamodel :=
               let hsm_as := (InitialState_getAbstractState is1) in
                let fsm_as := (BuildFAbstractState (AbstractState_getName hsm_as) (AbstractState_getAbstractStateID hsm_as)) in
                  BuildFInitialState fsm_as (InitialState_getInitialStateID is1)
             links
               nil
          ]
      ;

       rule IS2RS
         from
           element is1 class InitialStateEClass from HSMMetamodel
             when (negb (isNone CompositeState (AbstractState_getCompositeState (InitialState_getAbstractState is1) m)))
         to
          [
           output "rs2"
             element rs2 class FRegularStateEClass from FSMMetamodel :=
               let hsm_as := (InitialState_getAbstractState is1) in
                let fsm_as := (BuildFAbstractState (AbstractState_getName hsm_as) (AbstractState_getAbstractStateID hsm_as)) in
                  BuildFRegularState fsm_as (InitialState_getInitialStateID is1)
             links
               nil
          ]
       ;

       rule T2TA
         from
           element t1 class TransitionEClass from HSMMetamodel
             when  andb (negb (isComposite (Transition_getSource t1 m) m))
                        (negb (isComposite (Transition_getTarget t1 m) m))
         to
          [
           output "t2"
             element t2 class FTransitionEClass from FSMMetamodel :=
               BuildFTransition (Transition_getLabel t1) (Transition_getTransitionID t1)
             links
               [
                 reference FTransitionStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (Transition_getStateMachine t1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFTransitionStateMachine t2 fsm_sm 
               ]
          ]
  ].

(* Unset Printing Notations.*)
(* Print Class2Relational. *)
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition HSM2FSM := parseTransformation HSM2FSMConcrete.

       



(*

                 reference FTransitionSourceEReference from FSMMetamodel :=
                   hsm_tr_source <- (Transition_getStateMachine t1 m);
                   return None
*)
       
