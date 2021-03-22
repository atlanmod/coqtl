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

  Definition denoteOutput (type: TargetModelClass) (f: option TargetModelElement): option (denoteModelClass type) :=
      match f with
      | Some e => toModelClass type e
      | _ => None
      end.

  Definition denoteOutputList (type: TargetModelClass) (f: option (list TargetModelElement)): option (list (denoteModelClass type)) :=
      match f with
      | Some e => Some (flat_map (fun l:TargetModelElement => optionToList (toModelClass type l)) e)
      | _ => None
      end.

  Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement)
             (iter : nat) : option (denoteModelClass type) :=
    denoteOutput type (resolveIter' tls sm name sp iter).

  Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    denoteOutput type (resolve' tr sm name sp).

  Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    : option (list (denoteModelClass type)) :=
    denoteOutputList type (resolveAllIter' tr sm name sps iter).

  Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
    denoteOutputList type (resolveAll' tr sm name sps).
  
  Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list SourceModelElement)) : option (denoteModelClass type) :=
    denoteOutput type (maybeResolve' tr sm name sp).

  Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
    (type: TargetModelClass) (sp: option (list (list SourceModelElement))) : option (list (denoteModelClass type)) :=
    denoteOutputList type (maybeResolveAll' tr sm name sp).

End SemanticsNonagnostic.