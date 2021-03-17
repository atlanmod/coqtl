Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import Bool.
Require Import Arith.
Scheme Equality for list.

Section SemanticsNonagnostic.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).

  Fixpoint checkTypes (ses: list SourceModelElement) (scs: list SourceModelClass) : bool :=
    match ses, scs with
    | se::ses', sc::scs' => 
      match (toModelClass sc se) with
      | Some c => checkTypes ses' scs'
      | _ => false
      end
    | nil, nil => true
    | _, _ => false
    end.

  Definition evalGuardExpr (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    if (checkTypes sp (Rule_getInTypes r)) then
      @evalGuardExpr' SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink r sm sp
    else Some false.


  (* ** Resolve *)

  Definition TraceLink' := @TraceLink SourceModelElement TargetModelElement.

  Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
  let tls' := 
    filter (fun tl: TraceLink => (list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp)) tls in
  match (resolveIter' tls' sm name sp iter) with
  | Some e => (toModelClass type e)
  | _ => None
  end.

  Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    match (resolveIter' tr sm name sp 0) with
    | Some e => (toModelClass type e)
    | _ => None
    end.

  Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    : option (list (denoteModelClass type)) :=
    Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter tr sm name type l iter)) sps).

  Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
    resolveAllIter tr sm name type sps 0.
  
  Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list SourceModelElement)) : option (denoteModelClass type) :=
    match sp with 
    | Some sp' => resolve tr sm name type sp'
    | None => None
    end.

  Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list (list SourceModelElement))) : option (list (denoteModelClass type)) :=
    match sp with 
    | Some sp' => resolveAll tr sm name type sp'
    | None => None
    end.

End SemanticsNonagnostic.