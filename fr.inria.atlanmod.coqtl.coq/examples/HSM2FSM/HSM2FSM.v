Require Import Bool.
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

Definition isRegularState (e : option AbstractState) (m : HSMModel) : bool :=
 match e with
  | None => false
  | Some a => negb (isNone RegularState (AbstractState_downcastRegularState a m))
 end.

Definition isInitialState (e : option AbstractState) (m : HSMModel) : bool :=
 match e with
  | None => false
  | Some a => negb (isNone InitialState (AbstractState_downcastInitialState a m))
 end.

Definition isCompositeState (e : option AbstractState) (m : HSMModel) : bool :=
 match e with
  | None => false
  | Some a => negb (isNone CompositeState (AbstractState_downcastCompositeState a m))
 end.

Definition beq_AbstractState_option (tr_arg1 : option AbstractState) (tr_arg2 : option AbstractState) : bool :=
 match tr_arg1, tr_arg2 with
  | Some a1, Some a2 => beq_AbstractState a1 a2
  | _, _ => false
 end.

Definition beq_CompositeState_option (tr_arg1 : option CompositeState) (tr_arg2 : option CompositeState) : bool :=
 match tr_arg1, tr_arg2 with
  | Some a1, Some a2 => beq_CompositeState a1 a2
  | _, _ => false
 end.

Definition AbstractState_getName_option (a : option AbstractState) : string :=
 match a with
  | Some a1 => AbstractState_getName a1
  | _ => "EmptyString"
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
             when (negb (isCompositeState (Some as1) m))
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
             when  andb (negb (isCompositeState (Transition_getSource t1 m) m))
                        (negb (isCompositeState (Transition_getTarget t1 m) m))
         to
          [
           output "t2_t2ta"
             element t2 class FTransitionEClass from FSMMetamodel :=
               BuildFTransition (Transition_getLabel t1) (Transition_getTransitionID t1)
             links
               [
                 reference FTransitionStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (Transition_getStateMachine t1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFTransitionStateMachine t2 fsm_sm ;

                 reference FTransitionSourceEReference from FSMMetamodel :=
                   hsm_tr_source <- (Transition_getSource t1 m);
                   fsm_tr_source <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject hsm_tr_source];
                   return BuildFTransitionSource t2 fsm_tr_source ;

                 reference FTransitionTargetEReference from FSMMetamodel :=
                   hsm_tr_target <- (Transition_getTarget t1 m);
                   fsm_tr_target <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject hsm_tr_target];
                   return BuildFTransitionTarget t2 fsm_tr_target
               ]
          ]
       ;

       rule T2TB
         from
           element t1 class TransitionEClass,
           element src class CompositeStateEClass,
           element trg class AbstractStateEClass,
           element c class AbstractStateEClass from HSMMetamodel
             when   (negb (isCompositeState (Some trg) m)) &&
                    (negb (beq_AbstractState c (CompositeState_getAbstractState src))) &&
                     beq_AbstractState_option (Transition_getSource t1 m) (Some (CompositeState_getAbstractState src)) && 
                     beq_AbstractState_option (Transition_getTarget t1 m) (Some trg) &&
                     beq_CompositeState_option (AbstractState_getCompositeState c m) (Some src)

         to
          [
           output "t2_t2tb"
             element t2 class FTransitionEClass from FSMMetamodel :=
               BuildFTransition ((Transition_getLabel t1) ++ "_from_" ++ (AbstractState_getName c) ++ "_to_" ++ (AbstractState_getName trg)) (Transition_getTransitionID t1)
             links
               [
                 reference FTransitionStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (Transition_getStateMachine t1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFTransitionStateMachine t2 fsm_sm ;

                 reference FTransitionSourceEReference from FSMMetamodel :=
                   fsm_tr_source <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject c];
                   return BuildFTransitionSource t2 fsm_tr_source ;

                 reference FTransitionTargetEReference from FSMMetamodel :=
                   fsm_tr_target <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject trg];
                   return BuildFTransitionTarget t2 fsm_tr_target
               ]
          ]
       ;

       rule T2TC
         from
           element t1 class TransitionEClass,
           element src class AbstractStateEClass,
           element trg class CompositeStateEClass,
           element c class InitialStateEClass from HSMMetamodel
             when   (negb (isCompositeState (Some src) m)) &&
                     beq_AbstractState_option (Transition_getSource t1 m) (Some src) && 
                     beq_AbstractState_option (Transition_getTarget t1 m) (Some (CompositeState_getAbstractState trg))&&
                     beq_CompositeState_option (AbstractState_getCompositeState (InitialState_getAbstractState c) m) (Some trg)
         to
          [
           output "t2_t2tc"
             element t2 class FTransitionEClass from FSMMetamodel :=
               BuildFTransition ((Transition_getLabel t1) ++ "_from_" ++ (AbstractState_getName src) ++ "_to_" ++ (AbstractState_getName (InitialState_getAbstractState c))) (Transition_getTransitionID t1)
             links
               [
                 reference FTransitionStateMachineEReference from FSMMetamodel :=
                   hsm_sm <- (Transition_getStateMachine t1 m);
                   fsm_sm <- resolve HSM2FSM m "sm2" FStateMachineEClass [HSMMetamodel_toEObject hsm_sm];
                   return BuildFTransitionStateMachine t2 fsm_sm ;

                 reference FTransitionSourceEReference from FSMMetamodel :=
                   fsm_tr_source <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject src];
                   return BuildFTransitionSource t2 fsm_tr_source ;

                 reference FTransitionTargetEReference from FSMMetamodel :=
                   hsm_c_abstract <- Some (InitialState_getAbstractState c);
                   fsm_tr_target <- resolve HSM2FSM m "as2" FAbstractStateEClass [HSMMetamodel_toEObject hsm_c_abstract];
                   return BuildFTransitionTarget t2 fsm_tr_target
               ]
          ]
       
  ].






(* Unset Printing Notations.*)
(* Print HSM2FSMConcrete. *)
(* Compute maxArity (parseTransformation HSM2FSMConcrete). *)

Definition HSM2FSM := parseTransformation HSM2FSMConcrete.


