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


Definition HSM2HSMConcrete :=
  transformation HSM2HSM from HSMMetamodel to HSMMetamodel
    with m as HSMModel := [

       rule SM2SM
         from
           element sm1 class StateMachineEClass from HSMMetamodel
             when true
         to
          [
           output "sm2"
             element sm2 class StateMachineEClass from HSMMetamodel :=
               BuildStateMachine (StateMachine_getName sm1) (StateMachine_getStateMachineID sm1)
             links
               nil
          ]

  ].


Definition HSM2HSM := parseTransformation HSM2HSMConcrete.


