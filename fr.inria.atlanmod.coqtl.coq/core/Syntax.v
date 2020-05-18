Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.

Section Syntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** * Abstract Syntax **)

  (** ** Expression Types **)

  Definition outputReferenceTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    denoteFunction smm (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

  Definition outputPatternElementTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFunction smm (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
             (sclasses : list SourceModelClass) (itype: Type) :=
    denoteFunction smm (sclasses) (list itype).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction smm (sclasses) bool.

  (** ** Syntax Types **)

  Inductive MatchedOutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type :=
    BuildMatchedOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
        (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
        MatchedOutputPatternElement InElTypes IterType.

  Inductive MatchedRule : Type :=
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
          (SourceModel -> (iteratedListTypes InElTypes IterType))
          -> list (MatchedOutputPatternElement InElTypes IterType)
          -> MatchedRule.

  Inductive MatchedTransformation : Type :=
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.

  Inductive OutputPatternElementReference (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass): Type :=
    BuildOutputPatternElementReference :
      forall (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType OutRef)) ->
        OutputPatternElementReference InElTypes IterType OutType.

  Inductive OutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type :=
    BuildOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
        (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
        list (OutputPatternElementReference InElTypes IterType OutType)-> OutputPatternElement InElTypes IterType.

  Inductive Rule : Type :=
    BuildRule :
      (* name *) string ->
      (* from *) forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        (* for *)  -> forall (IterType: Type),
          (SourceModel -> (iteratedListTypes InElTypes IterType))
          (* to *) -> list (OutputPatternElement InElTypes IterType)
          -> Rule.

  Inductive Transformation : Type :=
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getRefType {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) : TargetModelReference :=
    match o with
      BuildOutputPatternElementReference _ _ _ y _ => y
    end.

  Definition OutputPatternElementReference_getOutputReference {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) :
    MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType (OutputPatternElementReference_getRefType o)).
  Proof.
    destruct o eqn:ho.
    exact o0.
  Defined.

  Definition OutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : string :=
    match o with
      BuildOutputPatternElement _ _ y _ _ _ => y
    end.

  Definition OutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with
      BuildOutputPatternElement _ _ _ y _ _ => y
    end.

  Definition OutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (OutputPatternElement_getOutType o)) :=
    match o with
      BuildOutputPatternElement _ _ _ _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
    match o with
      BuildOutputPatternElement _ _ _ _ _ y => y
    end.

  Definition Rule_getName (x : Rule) : string :=
    match x with
      BuildRule y _ _ _ _ _ => y
    end.

  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with
      BuildRule _ y _ _ _ _ => y
    end.

  Definition Rule_getGuard (x : Rule) :
    SourceModel -> (guardTypes (Rule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with
      BuildRule _ _ _ y _ _ => y
    end.

  Definition Rule_getIteratedList (x: Rule) :
    SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getOutputPattern (x : Rule) :
    list (OutputPatternElement (Rule_getInTypes x) (Rule_getIteratorType x)) :=
    match x with
      BuildRule _ _ _ _ _ y => y
    end.

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option (OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) :=
    find (fun(o:OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPattern r).

  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.

  Definition MatchedOutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : string :=
    match o with
      BuildMatchedOutputPatternElement _ _ y _ _ => y
    end.

  Definition MatchedOutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with
      BuildMatchedOutputPatternElement _ _ _ y _ => y
    end.

  Definition MatchedOutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (MatchedOutputPatternElement_getOutType o)) :=
    match o with
      BuildMatchedOutputPatternElement _ _ _ _ y => y
    end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with
      BuildMatchedRule y _ _ _ _ _ => y
    end.

  Definition MatchedRule_getInTypes (x : MatchedRule) : list SourceModelClass :=
    match x with
      BuildMatchedRule _ y _ _ _ _ => y
    end.

  Definition MatchedRule_getGuard (x : MatchedRule) :
    SourceModel -> (guardTypes (MatchedRule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getIteratorType (x : MatchedRule) : Type :=
    match x with
      BuildMatchedRule _ _ _ y _ _ => y
    end.

  Definition MatchedRule_getIteratedList (x: MatchedRule) :
    SourceModel -> (iteratedListTypes (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getOutputPattern (x : MatchedRule) :
    list (MatchedOutputPatternElement (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)) :=
    match x with
      BuildMatchedRule _ _ _ _ _ y => y
    end.

  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** ** Copying Matched Transformation *)

  Definition matchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: OutputPatternElement InElTypes IterType)
    : MatchedOutputPatternElement InElTypes IterType :=
    match x with
    | BuildOutputPatternElement _ _ c d e f => BuildMatchedOutputPatternElement InElTypes IterType c d e
    end.

  Definition matchRule (x: Rule) : MatchedRule :=
    match x with
    | BuildRule a b c d e f => BuildMatchedRule a b c d e (map matchOutputPatternElement f)
    end.

  Definition matchTransformation (x: Transformation) : MatchedTransformation :=
    match x with
    | BuildTransformation a => BuildMatchedTransformation (map matchRule a)
    end.

  Definition unmatchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: MatchedOutputPatternElement InElTypes IterType)
    : OutputPatternElement InElTypes IterType :=
    match x with
    | BuildMatchedOutputPatternElement _ _ c d e => BuildOutputPatternElement InElTypes IterType c d e nil
    end.

  Definition unmatchRule (x: MatchedRule) : Rule :=
    match x with
    | BuildMatchedRule a b c d e f => BuildRule a b c d e (map unmatchOutputPatternElement f)
    end.

  Definition unmatchTransformation (x: MatchedTransformation) : Transformation :=
    match x with
    | BuildMatchedTransformation a => BuildTransformation (map unmatchRule a)
    end.

End Syntax.

Arguments Rule {_ _ _ _} _ {_ _ _ _} _.
Arguments BuildRule {_ _ _ _} _ {_ _ _ _} _.

Arguments MatchedRule {_ _ _ _} _ {_ _ _ _} _.

Arguments Transformation {_ _ _ _} _ {_ _ _ _} _.
Arguments BuildTransformation {_ _ _ _} _ {_ _ _ _} _.

Arguments MatchedTransformation {_ _ _ _} _ {_ _ _ _} _.

Arguments BuildOutputPatternElement {_ _ _ _} _ {_ _ _ _} _ _ {_}.
Arguments BuildOutputPatternElementReference {_ _ _ _} _ {_ _ _ _} _ _ {_}.
