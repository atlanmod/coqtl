Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.

Section ConcreteSyntaxB.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink)
          (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink)
          (TraceLink := @TraceLink SourceModelElement TargetModelElement).

  (** ** Syntax **)

  Fixpoint denoteFunction (sclasses : list SourceModelClass) (otype: Type) :=
    match sclasses with
    | nil => otype
    | cons class classes' => (denoteModelClass class) -> denoteFunction classes' otype
    end.

  Definition outputReferenceTypes
  (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
  denoteFunction (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).

  Definition outputPatternElementTypes
  (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFunction (sclasses) (option (denoteModelClass tclass)).

  Definition iteratedListTypes
  (sclasses : list SourceModelClass) :=
    denoteFunction (sclasses) (option nat).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction (sclasses) (option bool).

  Inductive ConcreteOutputPatternElementReference (InTypes: list SourceModelClass) (OutType:TargetModelClass) : Type :=
    link :
    forall (OutRef: TargetModelReference),
        (list TraceLink -> nat -> SourceModel -> (outputReferenceTypes InTypes OutType OutRef)) ->
        ConcreteOutputPatternElementReference InTypes OutType.

  Inductive ConcreteOutputPatternElement (InTypes: list SourceModelClass) : Type :=
    elem :
      forall (OutType:TargetModelClass),
        string ->
         (nat -> SourceModel -> (outputPatternElementTypes InTypes OutType)) 
      -> (list (ConcreteOutputPatternElementReference InTypes OutType)) -> ConcreteOutputPatternElement InTypes.

  Inductive ConcreteRule : Type :=
    concreteRule :
      (* name *) string
      (* from *) -> forall (InTypes: list SourceModelClass),
        option (SourceModel -> (guardTypes InTypes))
      (* for *) -> option (SourceModel -> (iteratedListTypes InTypes))
      (* to *) -> (list (ConcreteOutputPatternElement InTypes))
      -> ConcreteRule.

  Inductive ConcreteTransformation : Type :=
    transformation :
      list ConcreteRule
      -> ConcreteTransformation.

(*  Definition ConcreteOutputPatternElementReference_getLinkExpr (o: ConcreteOutputPatternElementReference) : 
    list TraceLink -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink :=
    match o with
      buildConcreteOutputPatternElementReference y => y
    end.

  Definition ConcreteOutputPatternElement_getName (o: ConcreteOutputPatternElement) : string :=
    match o with
      buildConcreteOutputPatternElement y _ _ => y
    end.

  Definition ConcreteOutputPatternElement_getElementExpr (o: ConcreteOutputPatternElement) : nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement :=
    match o with
      buildConcreteOutputPatternElement _ y _ => y
    end.

  Definition ConcreteOutputPatternElement_getOutputElementReferences (o: ConcreteOutputPatternElement) :
    list ConcreteOutputPatternElementReference :=
    match o with
      buildConcreteOutputPatternElement _ _ y => y
    end.

  Definition ConcreteRule_getName (x : ConcreteRule) : string :=
    match x with
      buildConcreteRule y _ _ _ _ => y
    end.
  
  Definition ConcreteRule_getGuardExpr (x : ConcreteRule) : SourceModel -> (list SourceModelElement) -> option bool :=
    match x with
      buildConcreteRule _ _ y _ _ => y
    end.

  Definition ConcreteRule_getInTypes (x : ConcreteRule) : list SourceModelClass :=
    match x with
      buildConcreteRule _ y _ _ _ => y
    end.

  Definition ConcreteRule_getIteratorExpr (x : ConcreteRule) : SourceModel -> (list SourceModelElement) -> option nat :=
    match x with
      buildConcreteRule _ _ _ y _ => y
    end.

  Definition ConcreteRule_getConcreteOutputPatternElements (x : ConcreteRule) :
    list ConcreteOutputPatternElement :=
    match x with
      buildConcreteRule _ _ _ _ y => y
    end.

  Definition ConcreteRule_findConcreteOutputPatternElement (r: ConcreteRule) (name: string) : option ConcreteOutputPatternElement :=
    find (fun (o:ConcreteOutputPatternElement) => beq_string name (ConcreteOutputPatternElement_getName o))
         (ConcreteRule_getConcreteOutputPatternElements r).

  Definition ConcreteTransformation_getConcreteRules (x : ConcreteTransformation) : list ConcreteRule :=
    match x with buildConcreteTransformation y => y end.*)

End ConcreteSyntaxB.

Arguments transformation {_ _ _ _} _ {_ _ _ _} _.
Arguments concreteRule {_ _ _ _ _ _ _ _ _ _}.
Arguments elem {_ _ _ _ _ _ _ _ _ _}.
Arguments link {_ _ _ _ _ _ _ _ _ _}.

Declare Scope coqtlb.

(* Rule *)
Notation "'rule' rulename 'from' types 'where' guard 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtlb.

(* Rule without guard *)
Notation "'rule' rulename 'from' types 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (None) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtlb.

(* Rule without iterator *)
Notation "'rule' rulename 'from' types 'where' guard 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (None) outputpattern)
    (right associativity, at level 60):coqtlb.

(* Rule without guard and iterator *)
Notation "'rule' rulename 'from' types 'to' outputpattern " :=
  (concreteRule rulename types (None) (None) outputpattern)
    (right associativity, at level 60):coqtlb.