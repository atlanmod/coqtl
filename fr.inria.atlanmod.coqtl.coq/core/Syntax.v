Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.

(** * Syntax

      In this section, we introduce _one possible_ abstract syntax of the CoqTL transformation engine.  
      ---- *)

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).

  (** ** Traces 
  
         We introduce the concept of trace in the syntax to track relationship of a target element and 
         the source pattern that generates it   *)

  Inductive TraceLink : Type :=
    buildTraceLink : 
      (list SourceModelElement * nat * string)
      -> TargetModelElement
      -> TraceLink.

  Definition TraceLink_getSourcePattern (tl: TraceLink):=
    match tl with 
      buildTraceLink (sp, i, n) te => sp
    end.

  Definition TraceLink_getIterator (tl: TraceLink):=
    match tl with 
      buildTraceLink (sp, i, n) te => i
    end.

  Definition TraceLink_getName (tl: TraceLink):=
    match tl with 
      buildTraceLink (sp, i, n) te => n
    end.

  Definition TraceLink_getTargetElement (tl: TraceLink):=
    match tl with 
      buildTraceLink (sp, i, n) te => te
    end.

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
      (* types *) -> (list SourceModelClass)
      (* from *) -> (SourceModel -> (list SourceModelElement) -> option bool)
      (* for *) -> (SourceModel -> (list SourceModelElement) -> option nat)
      (* to *) -> (list OutputPatternElement)
      -> Rule.

  Definition Rule_getName (x : Rule) : string :=
    match x with
      buildRule y _ _ _ _ => y
    end.
  
  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with
      buildRule _ y _ _ _ => y
    end.
    
  Definition Rule_getGuardExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> option bool :=
    match x with
      buildRule _ _ y _ _ => y
    end.

  Definition Rule_getIteratorExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> option nat :=
    match x with
      buildRule _ _ _ y _ => y
    end.

  Definition Rule_getOutputPatternElements (x : Rule) :
    list OutputPatternElement :=
    match x with
      buildRule _ _ _ _ y => y
    end.

  (** find an output pattern element in a rule by the given name: *)

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
    find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
          (Rule_getOutputPatternElements r).

  (** *** Transformation *)

  Inductive Transformation : Type :=
    buildTransformation :
      list Rule
      -> Transformation.

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with buildTransformation y => y end.

End Syntax.

(* begin hide *)
Arguments TraceLink {_ _}.

Arguments Transformation {_ _ _ _ _}.
Arguments Rule {_ _ _ _ _}.
Arguments buildRule {_ _ _ _ _}.

Arguments buildTransformation {_ _ _ _ _}.

Arguments buildOutputPatternElement {_ _ _ _}.
Arguments buildOutputPatternElementReference {_ _ _ _}.
(* end hide *)
