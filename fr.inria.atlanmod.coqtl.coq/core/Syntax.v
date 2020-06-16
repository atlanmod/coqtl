Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.

Definition IteratorType := nat.

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** ** Syntax Types **)

  Inductive MatchedOutputPatternElement : Type :=
    BuildMatchedOutputPatternElement :
      string ->
        (IteratorType -> SourceModel -> (list SourceModelElement) -> option TargetModelElement)
        -> MatchedOutputPatternElement.

  Inductive MatchedRule : Type :=
    BuildMatchedRule :
      (* name *) string
      (* from *) -> (SourceModel -> (list SourceModelElement) -> option bool)
      (* for *) -> (SourceModel -> (list SourceModelElement) -> list IteratorType)
      (* to *) -> (list MatchedOutputPatternElement)
      -> MatchedRule.

  Inductive MatchedTransformation : Type :=
    BuildMatchedTransformation :
      list MatchedRule 
      -> MatchedTransformation.

  Inductive OutputPatternElementReference : Type :=
    BuildOutputPatternElementReference :
      (MatchedTransformation -> IteratorType -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink) 
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
    MatchedTransformation -> IteratorType -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink :=
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

  Definition MatchedOutputPatternElement_getName (o: MatchedOutputPatternElement) : string :=
    match o with
      BuildMatchedOutputPatternElement y _ => y
    end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with
      BuildMatchedRule y _ _ _ => y
    end.

  Definition MatchedRule_getOutputPatternElements (x : MatchedRule) :
    list MatchedOutputPatternElement :=
    match x with
      BuildMatchedRule _ _ _ y => y
    end.

  Definition MatchedRule_findOutputPatternElement (r: MatchedRule) (name: string) : option MatchedOutputPatternElement :=
    find (fun (o:MatchedOutputPatternElement) => beq_string name (MatchedOutputPatternElement_getName o))
         (MatchedRule_getOutputPatternElements r).

  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** ** Copying Matched Transformation *)

  Definition matchOutputPatternElement (x: OutputPatternElement)
    : MatchedOutputPatternElement :=
    match x with
    | BuildOutputPatternElement a b c  => BuildMatchedOutputPatternElement a b
    end.

  Definition matchRule (x: Rule) : MatchedRule :=
    match x with
    | BuildRule a b c d => BuildMatchedRule a b c (map matchOutputPatternElement d)
    end.

  Definition matchTransformation (x: Transformation) : MatchedTransformation :=
    match x with
    | BuildTransformation a => BuildMatchedTransformation (map matchRule a)
    end.

  Definition unmatchOutputPatternElement (x: MatchedOutputPatternElement)
    : OutputPatternElement :=
    match x with
    | BuildMatchedOutputPatternElement a b => BuildOutputPatternElement a b nil
    end.

  Definition unmatchRule (x: MatchedRule) : Rule :=
    match x with
    | BuildMatchedRule a b c d => BuildRule a b c (map unmatchOutputPatternElement d)
    end.

  Definition unmatchTransformation (x: MatchedTransformation) : Transformation :=
    match x with
    | BuildMatchedTransformation a => BuildTransformation (map unmatchRule a)
    end.

End Syntax.

Arguments Transformation {_ _ _ _}.
Arguments Rule {_ _ _ _}.
Arguments BuildRule {_ _ _ _}.

Arguments MatchedRule {_ _ _}.

Arguments BuildTransformation {_ _ _ _}.

Arguments MatchedTransformation {_ _ _}.

Arguments BuildOutputPatternElement {_ _ _ _}.
Arguments BuildOutputPatternElementReference {_ _ _ _}.
