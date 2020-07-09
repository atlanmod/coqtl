Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** ** Traces **)

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

  (** ** Syntax **)

  Inductive OutputPatternElementReference : Type :=
    buildOutputPatternElementReference :
      (list TraceLink -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink) 
      -> OutputPatternElementReference.

  Inductive OutputPatternElement : Type :=
    buildOutputPatternElement :
      string 
      -> (nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement) 
      -> (list OutputPatternElementReference) -> OutputPatternElement.

  Inductive Rule : Type :=
    buildRule :
      (* name *) string
      (* from *) -> (SourceModel -> (list SourceModelElement) -> option bool)
      (* for *) -> (SourceModel -> (list SourceModelElement) -> option nat)
      (* to *) -> (list OutputPatternElement)
      -> Rule.

  Inductive Transformation : Type :=
    buildTransformation :
      list Rule
      -> Transformation.

  Definition OutputPatternElementReference_getLinkExpr (o: OutputPatternElementReference) : 
    list TraceLink -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink :=
    match o with
      buildOutputPatternElementReference y => y
    end.

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

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
    find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPatternElements r).

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with buildTransformation y => y end.

End Syntax.

Arguments TraceLink {_ _}.

Arguments Transformation {_ _ _ _}.
Arguments Rule {_ _ _ _}.
Arguments buildRule {_ _ _ _}.

Arguments buildTransformation {_ _ _ _}.

Arguments buildOutputPatternElement {_ _ _ _}.
Arguments buildOutputPatternElementReference {_ _ _ _}.
