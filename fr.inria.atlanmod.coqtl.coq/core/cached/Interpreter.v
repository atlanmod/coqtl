Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import Bool.
Require Import core.Syntax.
Require Import Arith.
Require Import Semantics.
Require Import List.

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

    (* This is the statments that can be specified in our replay language 
       Remark: In Massimo's branch:
       - TransformationSystem is a tuple of: tr sm tm
       - It is an argument of each kind of stmt
        - it is a way to couple stmt with evaluation, i.e. evaluation on a stmt have all information it is needed.
        - the way here structure is to decouple stmt from evaluation, It looks clearer for now.
     *)

    (*Inductive Stmt : Type :=
    | skip : Stmt
    | seq : Stmt -> Stmt -> Stmt
    | addElementToSource : SourceModelElement -> Stmt
    | getRootFromTarget: Stmt
    | getFromTarget: TargetModelElement -> TargetModelReference -> Stmt
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
    | skip : Stmt
    .

    (* some helper of Model *)

    Definition Model_addElementToSource (sm: SourceModel) (se: SourceModelElement) := 
      Build_Model (se::(allModelElements sm)) 
                  (allModelLinks sm).

    Definition Model_addElementToTarget (tm: TargetModel) (te: TargetModelElement) := 
      Build_Model (te::(allModelElements tm)) 
                  (allModelLinks tm).

    Inductive state :=
    | error : state
    | conf : Transformation -> SourceModel -> TargetModel -> Stmt -> state.

    Definition state_getTransformation(s: state): option Transformation :=
    match s with 
    | conf tr _ _ _ => Some tr
    | _ => None
    end.

    Definition state_getSourceModel(s: state): option SourceModel :=
    match s with 
    | conf tr sm _ _ => Some sm
    | _ => None
    end.

    Definition state_getTargetModel(s: state): option TargetModel :=
    match s with 
    | conf tr sm tm _ => Some tm
    | _ => None
    end.

    Definition state_getStmt (s: state): option Stmt :=
    match s with 
    | conf tr sm tm stmt => Some stmt
    | _ => None
    end.

    (* default semantics *)

    (* step : state -> state 
     *)
    
    Definition strict_replay (s: Stmt) (st: State) : State * (option (list TargetModelElement)) :=
      match s with
      | getRootFromTarget => (st, Some nil) (* accessing the function of the State typeclass *)
      | _ => (st, None)
      end.

    Definition strict_replay_state (s: Stmt) (st: State) := (fst (strict_replay s st)).

    Definition strict_replay_trace_state (st: State) (s: list Stmt) :=
      fold_right strict_replay_state st s.

    Definition replay_last_output (st: State) (s: list Stmt) :=
      let endstate := fold_right (strict_replay_state) st (removelast s) in
        (snd (strict_replay (last s skip) endstate)).
      
    (* Theorem equivalence_strict_lazy:
      forall (st: State) (trace: list Stmt),
        list_beq (strict_replay_trace st trace) (lazy_replay_trace st trace).*)

    (*Theorem equivalence_strict_lazy:
      forall (st: State) (trace: list Stmt),
        beq (strict_replay_last_output st trace) (lazy_replay_last_output st trace).*)

    Definition strict_replay' (s: Stmt) (st: State) : State :=
      match s with
      | getRootFromTarget => st (* accessing the function of the State typeclass *)
      | _ => st
      end.

    Definition strict_replay_trace_state' (st: State) (s: list Stmt) :=
      fold_right strict_replay' st s.

    (*Definition replay_last_output' (st: State) (s: list Stmt) :=
      let endstate := fold_right (strict_replay') st (removelast s) in
        match (last s skip) with 
        | getRootFromTarget => None
        | _ => None
        end.*)
      
    (* Theorem equivalence_strict_lazy:
      forall (st: State) (trace: list Stmt),
        list_beq (strict_replay_trace st trace) (lazy_replay_trace st trace).*)

    Theorem equivalence_strict_lazy:
      forall (st: State) (trace: list Stmt),
        beq (strict_replay_last_output st trace) (lazy_replay_last_output st trace).

    Fixpoint replay  (tr: Transformation) (sm: SourceModel) (tm: TargetModel) (s: Stmt) : state :=
      match s with
      | seq s1 s2 => 
          match s1 with
          | skip => conf tr sm tm s2
          | _ => match replay tr sm tm s1 with
                  | error => error
                  | conf tr2 sm2 tm2 s1_ => conf tr2 sm2 tm2 (seq s1_ s2)
                 end
          end
      | addElementToSource se => conf tr (Model_addElementToSource sm se) (execute tr (Model_addElementToSource sm se)) skip
      | _ => error
      end.

    (* lazy semantics *)

    (* the output model of addElementToSource is different between lazy and strict, but they output the same modelelement *)

    Definition smartTuples (tr: Transformation) (sm: SourceModel) (se: SourceModelElement) : list (list SourceModelElement):= nil.

    Theorem tuple_equiv :
      forall (tr: Transformation) (sm: SourceModel) (se: SourceModelElement) (sp: list SourceModelElement), 
        In sp (allTuples tr ((Model_addElementToSource sm se))) <-> In sp (smartTuples tr sm se) \/ In sp (allTuples tr sm).

    Fixpoint replay_lazy (tr: Transformation) (sm: SourceModel) (tm: TargetModel) (s: Stmt) :=
      match s with
      | addElementToSource se => 
          let tm_ := (execute tr sm) in
            let tes := (flat_map (instantiatePattern tr sm) (smartTuples tr sm se)) in
            conf tr (Model_addElementToSource sm se) 
                 (Build_Model (tes ++ (allModelElements tm_)) (allModelLinks tm_))
                 skip
      | _ => replay tr sm tm s
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
