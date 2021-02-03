Require Import String.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import core.Expressions.

Section ConcreteSyntax.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink SourceModelClass TargetModelElement TargetModelLink).
  Context (TraceLink := @TraceLink SourceModelElement TargetModelElement).

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
    denoteFunction (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
  (sclasses : list SourceModelClass) :=
    denoteFunction (sclasses) nat.

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction (sclasses) bool.

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

  (** ** Accessors **)

  Definition ConcreteOutputPatternElementReference_getRefType {InElTypes: list SourceModelClass} {OutType:TargetModelClass} (o: ConcreteOutputPatternElementReference InElTypes OutType) : TargetModelReference :=
    match o with
      link _ _ y _ => y
    end.

  Definition ConcreteOutputPatternElementReference_getOutputReference {InElTypes: list SourceModelClass} {OutType:TargetModelClass} (o: ConcreteOutputPatternElementReference InElTypes OutType) :
    list TraceLink -> nat -> SourceModel -> (outputReferenceTypes InElTypes OutType (ConcreteOutputPatternElementReference_getRefType o)).
  Proof.
    destruct o eqn:ho.
    exact o0.
  Defined.

  Definition ConcreteOutputPatternElement_getName {InElTypes: list SourceModelClass} (o: ConcreteOutputPatternElement InElTypes) : string :=
    match o with
      elem _ _ y _ _ => y
    end.

  Definition ConcreteOutputPatternElement_getOutType {InElTypes: list SourceModelClass} (o: ConcreteOutputPatternElement InElTypes) : TargetModelClass :=
    match o with
      elem _ y _ _ _ => y
    end.

  Definition ConcreteOutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} (o: ConcreteOutputPatternElement InElTypes) :
    nat -> SourceModel -> (outputPatternElementTypes InElTypes (ConcreteOutputPatternElement_getOutType o)) :=
    match o with
      elem _ _ _ y _ => y
    end.

  Definition ConcreteOutputPatternElement_getOutputElementReferences {InElTypes: list SourceModelClass} (o: ConcreteOutputPatternElement InElTypes) :
    list (ConcreteOutputPatternElementReference InElTypes (ConcreteOutputPatternElement_getOutType o)) :=
    match o with
      elem _ _ _ _ y => y
    end.

  Definition ConcreteRule_getName (x : ConcreteRule) : string :=
    match x with
      concreteRule y _ _ _ _ => y
    end.

  Definition ConcreteRule_getInTypes (x : ConcreteRule) : list SourceModelClass :=
    match x with
      concreteRule _ y _ _ _ => y
    end.

  Definition ConcreteRule_getGuard (x : ConcreteRule) :
    option(SourceModel -> (guardTypes (ConcreteRule_getInTypes x))).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition ConcreteRule_getIteratedList (x: ConcreteRule) :
    option (SourceModel -> (iteratedListTypes (ConcreteRule_getInTypes x))).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition ConcreteRule_getConcreteOutputPattern (x : ConcreteRule) :
    list (ConcreteOutputPatternElement (ConcreteRule_getInTypes x)) :=
    match x with
      concreteRule _ _ _ _ y => y
    end.

  Definition ConcreteRule_findConcreteOutputPatternElement (r: ConcreteRule) (name: string) : option (ConcreteOutputPatternElement (ConcreteRule_getInTypes r)) :=
    find (fun(o:ConcreteOutputPatternElement (ConcreteRule_getInTypes r)) => beq_string name (ConcreteOutputPatternElement_getName o))
         (ConcreteRule_getConcreteOutputPattern r).

  Definition ConcreteTransformation_getConcreteRules (x : ConcreteTransformation) : list ConcreteRule :=
    match x with transformation y => y end.

  Definition parseOutputPatternElementReference (intypes: list SourceModelClass) (outtype: TargetModelClass)
    (cr: ConcreteOutputPatternElementReference intypes outtype): OutputPatternElementReference :=
    buildOutputPatternElementReference 
      (makeLink intypes outtype (ConcreteOutputPatternElementReference_getRefType cr) (ConcreteOutputPatternElementReference_getOutputReference cr)).

  Definition parseOutputPatternElement (intypes: list SourceModelClass) (co: ConcreteOutputPatternElement intypes) : OutputPatternElement :=
    buildOutputPatternElement
      (ConcreteOutputPatternElement_getName co)
      (makeElement intypes (ConcreteOutputPatternElement_getOutType co) (ConcreteOutputPatternElement_getOutPatternElement co))
      (map (parseOutputPatternElementReference intypes (ConcreteOutputPatternElement_getOutType co)) (ConcreteOutputPatternElement_getOutputElementReferences co)).

  Definition parseRule(cr: ConcreteRule) : Rule :=
    buildRule
      (ConcreteRule_getName cr)
      (ConcreteRule_getInTypes cr)
      (match ConcreteRule_getGuard cr with
      | Some g => (makeGuard (ConcreteRule_getInTypes cr) g)
      | None => (fun _ _ => Some true)
      end)
      (match ConcreteRule_getIteratedList cr with
      | Some i => (makeIterator (ConcreteRule_getInTypes cr) i)
      | None => (fun _ _ => Some 1)
      end)
      (map (parseOutputPatternElement (ConcreteRule_getInTypes cr)) (ConcreteRule_getConcreteOutputPattern cr)).
  
  Definition parse(ct: ConcreteTransformation) : Transformation :=
    buildTransformation 
      (map parseRule (ConcreteTransformation_getConcreteRules ct)).

End ConcreteSyntax.

Arguments transformation {_ _ _ _} _ {_ _ _ _} _.
Arguments concreteRule {_ _ _ _ _ _ _ _ _ _}.
Arguments elem {_ _ _ _ _ _ _ _ _ _}.
Arguments link {_ _ _ _ _ _ _ _ _ _}.

Declare Scope coqtl.

(* Rule *)
Notation "'rule' rulename 'from' types 'where' guard 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard *)
Notation "'rule' rulename 'from' types 'for' iterator 'to' outputpattern " :=
  (concreteRule rulename types (None) (Some iterator) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without iterator *)
Notation "'rule' rulename 'from' types 'where' guard 'to' outputpattern " :=
  (concreteRule rulename types (Some guard) (None) outputpattern)
    (right associativity, at level 60):coqtl.

(* Rule without guard and iterator *)
Notation "'rule' rulename 'from' types 'to' outputpattern " :=
  (concreteRule rulename types (None) (None) outputpattern)
    (right associativity, at level 60):coqtl.