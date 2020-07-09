Require Import String.

Require Import core.utils.TopUtils.
Require Import core.Syntax.
Require Import core.Metamodel.
Require Import core.Model.

Definition IteratorType := nat.

Section Expressions.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}
          {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}
          {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}
          {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}
          (SourceModel := Model SourceModelElement SourceModelLink)
          (TargetModel := Model TargetModelElement TargetModelLink).

  (** ** Generic functions generation *)

  Fixpoint denoteSignature (l : list SourceModelClass) (r : Type) : Type :=
    match l with
    | nil => r
    | l0 :: l' => denoteModelClass l0 -> denoteSignature l' r
    end.

  Definition wrapOption {T : Type}
    (l : list SourceModelClass)
    (imp : denoteSignature l (option T)) :
    (list SourceModelElement) -> option T.
  Proof.
    revert l imp. fix Hl 1. intros l imp sl.
    destruct l as [ | l0 l'], sl as [ | s0 sl'].
    - exact imp.
    - exact None.
    - exact None.
    - exact (x <- toModelClass l0 s0; Hl l' (imp x) sl').
  Defined.

  Definition wrapList {T : Type} (l : list SourceModelClass)
    (imp : denoteSignature l (list T)) :
    (list SourceModelElement) -> list T.
  Proof.
    revert l imp. fix Hl 1. intros l imp sl.
    destruct l as [ | l0 l'], sl as [ | s0 sl'].
    - exact imp.
    - exact nil.
    - exact nil.
    - destruct (toModelClass l0 s0) as [x | ].
      + exact (Hl l' (imp x) sl').
      + exact nil.
  Defined.

  Definition wrapOptionElement
    (l : list SourceModelClass) (t : TargetModelClass)
    (imp : denoteSignature l (option (denoteModelClass t))) :
    (list SourceModelElement) -> option TargetModelElement.
  Proof.
    revert l imp. fix Hl 1. intros l imp sl.
    destruct l as [ | l0 l'], sl as [ | s0 sl'].
    - exact (x <- imp ; return (toModelElement t x)).
    - exact None.
    - exact None.
    - exact (x0 <- toModelClass l0 s0; Hl l' (imp x0) sl').
  Defined.

  Definition wrapOptionLink
    (l : list SourceModelClass) (t : TargetModelClass) (r : TargetModelReference)
    (imp : denoteSignature l (denoteModelClass t -> option (denoteModelReference r))) :
    (list SourceModelElement) -> TargetModelElement -> option TargetModelLink.
  Proof.
    revert l imp. fix Hl 1. intros l imp sl v.
    destruct l as [ | l0 l'], sl as [ | s0 sl'].
    - refine (xv <- toModelClass t v; xr <- imp xv; return (toModelLink r xr)).
    - exact None.
    - exact None.
    - exact (x0 <- toModelClass l0 s0; Hl l' (imp x0) sl' v).
  Defined.

  Definition GuardFunction : Type :=
    SourceModel -> (list SourceModelElement) -> option bool.
  Definition makeGuard (l : list SourceModelClass)
    (imp : SourceModel -> denoteSignature l (option bool)) :
    GuardFunction :=
    fun sm => wrapOption l (imp sm).

  Definition IteratorFunction : Type :=
    SourceModel -> (list SourceModelElement) -> list IteratorType.
  Definition makeIterator (l : list SourceModelClass)
    (imp : SourceModel -> denoteSignature l (list IteratorType)) :
    IteratorFunction :=
    fun sm => wrapList l (imp sm).

  Definition ElementFunction : Type :=
    IteratorType -> SourceModel -> (list SourceModelElement) -> option TargetModelElement.
  Definition makeElement (l : list SourceModelClass) (t : TargetModelClass)
    (imp : IteratorType -> SourceModel -> denoteSignature l (option (denoteModelClass t))) :
    ElementFunction :=
    fun it sm => wrapOptionElement l t (imp it sm).

  Definition LinkFunction : Type :=
    list (@TraceLink SourceModelElement TargetModelElement)
    -> IteratorType -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option TargetModelLink.
  Definition makeLink (l : list SourceModelClass) (t : TargetModelClass) (r : TargetModelReference)
    (imp : list TraceLink -> IteratorType -> SourceModel -> denoteSignature l (denoteModelClass t -> option (denoteModelReference r))) :
    LinkFunction :=
    fun mt it sm => wrapOptionLink l t r (imp mt it sm).

End Expressions.