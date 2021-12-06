Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.modeling.ConcreteSyntax.
Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.EqDec. 
Require Import core.modeling.Parser.
Require Import Bool.
Require Import Arith.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Scheme Equality for list.

Section SemanticsModeling.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(*Fixpoint checkTypes (ses: list SourceModelElement) (scs: list SourceModelClass) : bool :=
  match ses, scs with
  | se::ses', sc::scs' => 
    match (toModelClass sc se) with
    | Some c => checkTypes ses' scs'
    | _ => false
    end
  | nil, nil => true
  | _, _ => false
  end.*)

(*Definition evalGuardExpr (r : ConcreteRule (smm:=smm)) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
  if (checkTypes sp (ConcreteRule_getInTypes (smm:=smm) r)) then
    @evalGuardExpr' SourceModelElement SourceModelLink TargetModelElement TargetModelLink (parseRule r) sm sp
  else Some false. *)

(* ** Resolve *)

(*Definition TraceLink' := @TraceLink SourceModelElement TargetModelElement.*)

Definition denoteOutput (type: TargetModelClass) (f: option TargetModelElement): option (denoteModelClass type) :=
    match f with
    | Some e => toModelClass type e
    | _ => None
    end.

Definition denoteOutputList (type: TargetModelClass) (f: option (list TargetModelElement)): option (list (denoteModelClass type)) :=
    match f with
    | Some l => Some (flat_map (fun e:TargetModelElement => optionToList (toModelClass type e)) l)
    | _ => None
    end.


Definition resolveIter (tls: list TraceLink) (sm: SourceModel) (name: string)
            (type: TargetModelClass) (sp: list SourceModelElement)
            (iter : nat) : option (denoteModelClass type) :=
  denoteOutput type (resolveIter tls sm name sp iter).

Definition resolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
  denoteOutput type (resolve tr sm name sp).

Definition resolveAllIter (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
  : option (list (denoteModelClass type)) :=
  denoteOutputList type (resolveAllIter tr sm name sps iter).

Definition resolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
  denoteOutputList type (resolveAll tr sm name sps).

Definition maybeResolve (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetModelClass) (sp: option (list SourceModelElement)) : option (denoteModelClass type) :=
  denoteOutput type (maybeResolve tr sm name sp).

Definition maybeResolveAll (tr: list TraceLink) (sm: SourceModel) (name: string)
  (type: TargetModelClass) (sp: option (list (list SourceModelElement))) : option (list (denoteModelClass type)) :=
  denoteOutputList type (maybeResolveAll tr sm name sp).

End SemanticsModeling.