Require Import String.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Export core.TraceLink.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section Syntax.

Context {tc: TransformationConfiguration}.

(** ** Syntactic Elements

        Next, we model syntactic elements of any transformation specification that supported by the CoqTL engine. *)

(** *** OutputPatternElementReference *)

Inductive OutputPatternElementReference : Type :=
  buildOutputPatternElementReference :
    (list TraceLink -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink) 
    -> OutputPatternElementReference.

Definition OutputPatternElementReference_getLinkExpr (o: OutputPatternElementReference) : 
    list TraceLink -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink :=
    match o with
      buildOutputPatternElementReference y => y
    end.

(** *** OutputPatternElement *)

Inductive OutputPatternElement : Type :=
  buildOutputPatternElement :
    string 
    -> (nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement) 
    -> (list OutputPatternElementReference) -> OutputPatternElement.

Definition OutputPatternElement_getName (o: OutputPatternElement) : string :=
  match o with
    buildOutputPatternElement y _ _ => y
  end.

Definition OutputPatternElement_getElementExpr (o: OutputPatternElement) : nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement :=
  match o with
    buildOutputPatternElement _ y _ => y
  end.

Definition OutputPatternElement_getOutputElementReferences (o: OutputPatternElement) :
  list OutputPatternElementReference :=
  match o with
    buildOutputPatternElement _ _ y => y
      end.

(** *** Rule *)

Inductive Rule : Type :=
  buildRule :
    (* name *) string
    (* from *) -> (SourceModel -> (list SourceModelElement) -> option bool)
    (* for *) -> (SourceModel -> (list SourceModelElement) -> option nat)
    (* to *) -> (list OutputPatternElement)
    -> Rule.

Definition Rule_getName (x : Rule) : string :=
  match x with
    buildRule y _ _ _ => y
  end.
  
Definition Rule_getGuardExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> option bool :=
  match x with
    buildRule _ y _ _ => y
  end.

Definition Rule_getIteratorExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> option nat :=
  match x with
    buildRule _ _ y _ => y
  end.

Definition Rule_getOutputPatternElements (x : Rule) :
  list OutputPatternElement :=
  match x with
    buildRule _ _ _ y => y
  end.

(** find an output pattern element in a rule by the given name: *)

Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
  find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
        (Rule_getOutputPatternElements r).

(** *** Transformation *)

Inductive Transformation : Type :=
  buildTransformation :
    nat
    -> list Rule
    -> Transformation.

Definition Transformation_getArity (x : Transformation) : nat :=
  match x with buildTransformation y _ => y end.

Definition Transformation_getRules (x : Transformation) : list Rule :=
  match x with buildTransformation _ y => y end.

End Syntax.

(* begin hide *)
Arguments Transformation {_}.
Arguments buildTransformation {_}.

Arguments Rule {_}.
Arguments buildRule {_}.

Arguments buildOutputPatternElement {_}.
Arguments buildOutputPatternElementReference {_}.
(* end hide *)
