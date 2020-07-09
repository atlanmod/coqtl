Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.

Definition IteratorType := nat.

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** ** Traces **)

  Inductive TraceLink : Type :=
    BuildTraceLink : 
      (list SourceModelElement * nat * string)
      -> TargetModelElement
      -> TraceLink.

  Definition TraceLink_getSourcePattern (tl: TraceLink):=
    match tl with 
      BuildTraceLink (sp, i, n) te => sp
    end.

  Definition TraceLink_getIterator (tl: TraceLink):=
    match tl with 
      BuildTraceLink (sp, i, n) te => i
    end.

  Definition TraceLink_getName (tl: TraceLink):=
    match tl with 
      BuildTraceLink (sp, i, n) te => n
    end.

  Definition TraceLink_getTargetElement (tl: TraceLink):=
    match tl with 
      BuildTraceLink (sp, i, n) te => te
    end.

  (** ** Syntax **)

  Inductive OutputPatternElementReference : Type :=
    BuildOutputPatternElementReference :
      (list TraceLink -> IteratorType -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink) 
      -> OutputPatternElementReference.

  Inductive OutputPatternElement : Type :=
    BuildOutputPatternElement :
      string 
      -> (IteratorType -> SourceModel -> (list SourceModelElement) -> option TargetModelElement) 
      -> (list OutputPatternElementReference) -> OutputPatternElement.

  Inductive Rule : Type :=
    BuildRule :
      (* name *) string
      (* from *) -> (SourceModel -> (list SourceModelElement) -> option bool)
      (* for *) -> (SourceModel -> (list SourceModelElement) -> list IteratorType)
      (* to *) -> (list OutputPatternElement)
      -> Rule.

  Inductive Transformation : Type :=
    BuildTransformation :
      list Rule
      -> Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getLinkExpr (o: OutputPatternElementReference) : 
    list TraceLink -> IteratorType -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink :=
    match o with
      BuildOutputPatternElementReference y => y
    end.

  Definition OutputPatternElement_getName (o: OutputPatternElement) : string :=
    match o with
      BuildOutputPatternElement y _ _ => y
    end.

  Definition OutputPatternElement_getElementExpr (o: OutputPatternElement) : IteratorType -> SourceModel -> (list SourceModelElement) -> option TargetModelElement :=
    match o with
      BuildOutputPatternElement _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences (o: OutputPatternElement) :
    list OutputPatternElementReference :=
    match o with
      BuildOutputPatternElement _ _ y => y
    end.

  Definition Rule_getName (x : Rule) : string :=
    match x with
      BuildRule y _ _ _ => y
    end.
  
  Definition Rule_getGuardExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> option bool :=
    match x with
      BuildRule _ y _ _ => y
    end.

  Definition Rule_getIteratorExpr (x : Rule) : SourceModel -> (list SourceModelElement) -> list IteratorType :=
    match x with
      BuildRule _ _ y _ => y
    end.

  Definition Rule_getOutputPatternElements (x : Rule) :
    list OutputPatternElement :=
    match x with
      BuildRule _ _ _ y => y
    end.

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option OutputPatternElement :=
    find (fun (o:OutputPatternElement) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPatternElements r).

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.

End Syntax.

Arguments TraceLink {_ _}.

Arguments Transformation {_ _ _ _}.
Arguments Rule {_ _ _ _}.
Arguments BuildRule {_ _ _ _}.

Arguments BuildTransformation {_ _ _ _}.

Arguments BuildOutputPatternElement {_ _ _ _}.
Arguments BuildOutputPatternElementReference {_ _ _ _}.
