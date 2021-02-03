Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import Bool.
Require Import core.Syntax.
Require Import Arith.
Require Import Semantics.

Scheme Equality for list.


(* execute the rule completely [in terms of both instantiate and apply]
   the basic unit is a task, or a source pattern, we want to finish each task asap.
   or, we could chose the basic unit to be rule, we want then to finish each rule asap.

   it is a good strategy if we want some task to be processed first, instead of waiting for whole instantiate finished
 *)

Section LazySemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

    (* This is the statments that can be specified in our replay language, TODO: check the arg of each STMT *)

    (*Inductive Stmt : Type :=
    | skip : Stmt
    | seq : Stmt -> Stmt -> Stmt
    | addElementToSource : SourceModelElement -> Stmt
    | getRootFromTarget: SourceModel -> Stmt
    | getFromTarget : SourceModel -> SourceModelClass -> Stmt
    | deleteElementFromSource : SourceModelElement -> Stmt
    | addLinkToSource : SourceModelLink -> Stmt
    | deleteLinkFromSource : SourceModelLink -> Stmt.*)

    Inductive Stmt : Type :=
    | apply : Stmt
    | getFromTarget : TargetModelElement -> TargetModelReference -> Stmt
    | getRootFromTarget : Stmt
    | addElementToSource : SourceModelElement -> Stmt
    | deleteElementFromSource : SourceModelElement -> Stmt
    | addLinkToSource : SourceModelLink -> Stmt
    .

    (* some helper of Model *)

    Definition Model_addElementToSource (sm: SourceModel) (se: SourceModelElement) := 
      Build_Model (se::(allModelElements sm)) 
                  (allModelLinks sm).

    Inductive state :=
    | error : state
    | finish : state
    | conf : Transformation -> SourceModel -> TargetModel -> Stmt -> state.

    Inductive State.

    (* default semantics *)

    (* step : state -> state 
       TODO: step : state -> state * output, this signature can show the output of the trace
     *)
    
    Definition replay (s: Stmt) (st: State) : State * (option (list TargetModelElement)) :=
      match s with
      | _ => (st, None)
      end.
    
    Definition replay_state (s: Stmt) (st: State) := (fst (replay s st)).

    Definition replay_prog_state (st: State) (s: list Stmt) :=
      fold_right (replay_state) st s.
      
    Definition strict_replay_trace (st: State) (tr: list Stmt) : list (option (list TargetModelElement)) :=
      nil.

    Definition lazy_replay_trace (st: State) (tr: list Stmt) : list (option (list TargetModelElement)) :=
      nil.

    Theorem equivalence_strict_lazy:
      forall (st: State) (trace: list Stmt),
        beq_list (strict_replay_prog st trace) (lazy_replay_prog st trace).
        

    Fixpoint replay (tr: Transformation) (sm: SourceModel) (tm: TargetModel) (s: Stmt) : state :=
      match s with
      | skip => finish tm (* print getroot ? *)
      | seq s1 s2 => error
      | addElementToSource se => conf tr (Model_addElementToSource sm se) (execute tr (Model_addElementToSource sm se)) skip
      | _ => error
      end.




    (* lazy semantics *)

    Fixpoint replay_lazy (tr: Transformation) (sm: SourceModel) (tm: TargetModel) (s: Stmt) :=
      match s with
      | skip => error
      | seq s1 s2 => error
      | addElementToSource se => error
      | _ => error
      end.

    (* sample program *)

    Variable se : SourceModelElement.
    Variable sm : SourceModel.
    Variable tr : Transformation.

    Definition exProg :=
    seq (seq (addElementToSource se)  (* <- output *)
             (getRootFromTarget sm))  (* <- output *)
        (getRootFromTarget sm).       (* <- output *)

    (* sample execution *)

    Definition trace :=
     replay tr sm (execute tr sm) exProg.



End LazySemantics.
