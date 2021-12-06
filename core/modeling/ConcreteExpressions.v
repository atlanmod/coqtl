Require Import String.

Require Import core.utils.Utils.
Require Import core.Syntax.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

Section ConcreteExpressions.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}.  

(** ** Generic functions generation *)

Fixpoint denoteSignature (l : list SourceModelClass) (r : Type) : Type :=
  match l with
  | nil => r
  | l0 :: l' => denoteModelClass l0 -> denoteSignature l' r
  end.

Definition wrapOption {T : Type}
  (l : list SourceModelClass)
  (imp : denoteSignature l T) :
  (list SourceModelElement) -> option T.
Proof.
  revert l imp. fix Hl 1. intros l imp sl.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - exact (Some imp).
  - exact None.
  - exact None.
  - exact (x <- toModelClass l0 s0; Hl l' (imp x) sl').
Defined.

Definition wrapOption' 
(l : list SourceModelClass) :
(list SourceModelElement) -> option bool.
Proof.
  revert l. fix Hl 1. intros l sl.
  destruct l as [ | l0 l'] eqn:a, sl as [ | s0 sl'] eqn:B.
  - exact (Some true).
  - exact None.
  - exact None.
  - exact (x <- toModelClass l0 s0; Hl l' sl').
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
  (imp : denoteSignature l (denoteModelClass t)) :
  (list SourceModelElement) -> option TargetModelElement.
Proof.
  revert l imp. fix Hl 1. intros l imp sl.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - exact (Some (toModelElement t imp)).
  - exact None.
  - exact None.
  - exact (x0 <- toModelClass l0 s0; Hl l' (imp x0) sl').
Defined.

Definition wrapOptionLink
  (l : list SourceModelClass) (t : TargetModelClass) (r : TargetModelReference)
  (imp : denoteSignature l (denoteModelClass t -> option (denoteModelReference r))) :
  (list SourceModelElement) -> TargetModelElement -> option (list TargetModelLink).
Proof.
  revert l imp. fix Hl 1. intros l imp sl v.
  destruct l as [ | l0 l'], sl as [ | s0 sl'].
  - refine (xv <- toModelClass t v; xr <- imp xv; return [toModelLink r xr]).
  - exact None.
  - exact None.
  - exact (x0 <- toModelClass l0 s0; Hl l' (imp x0) sl' v).
Defined.

Definition GuardFunction : Type :=
  SourceModel -> (list SourceModelElement) -> option bool.
Definition makeGuard (l : list SourceModelClass)
  (imp : SourceModel -> denoteSignature l bool) :
  GuardFunction :=
  fun sm => wrapOption l (imp sm).
Definition makeEmptyGuard (l : list SourceModelClass) : GuardFunction :=
  fun sm => wrapOption' l.

Definition IteratorFunction : Type :=
  SourceModel -> (list SourceModelElement) -> option nat.
Definition makeIterator (l : list SourceModelClass)
  (imp : SourceModel -> denoteSignature l nat) :
  IteratorFunction :=
  fun sm => wrapOption l (imp sm).

Definition ElementFunction : Type :=
  nat -> SourceModel -> (list SourceModelElement) -> option TargetModelElement.
Definition makeElement (l : list SourceModelClass) (t : TargetModelClass)
  (imp : nat -> SourceModel -> denoteSignature l (denoteModelClass t)) :
  ElementFunction :=
  fun it sm => wrapOptionElement l t (imp it sm).

Definition LinkFunction : Type :=
  list TraceLink
  -> nat -> SourceModel -> (list SourceModelElement) -> TargetModelElement -> option (list TargetModelLink).
Definition makeLink (l : list SourceModelClass) (t : TargetModelClass) (r : TargetModelReference)
  (imp : list TraceLink -> nat -> SourceModel -> denoteSignature l (denoteModelClass t -> option (denoteModelReference r))) :
  LinkFunction :=
  fun mt it sm => wrapOptionLink l t r (imp mt it sm).

End ConcreteExpressions.