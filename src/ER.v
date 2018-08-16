Section ER.

(* Coq libraries *)

Require Import Omega.
Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

(* EMF teminologies *)
Definition EClass := Set.

(* ER Metamodel *)

Inductive
  ERSchema : EClass :=
  BuildERSchema :
    (*oid*) nat ->
    (*name*) string ->
    (*entities*) list Entity ->
    (*relships*) list Relship -> ERSchema  
with
  Entity : EClass :=
  BuildEntity :
    (*oid*) nat -> 
    (*name*) string ->
    (*attrs*) list Attribute ->
    (*ends*) list RelshipEnd -> Entity
with
  Relship : EClass :=
  BuildRelship :
    (*oid*) nat -> 
    (*name*) string ->
    (*attrs*) list Attribute -> 
    (*ends*) list RelshipEnd -> Relship
with
  Attribute : EClass :=
  BuildAttribute :
    (*oid*) nat -> 
    (*name*) string ->
    (*isKey*) bool -> Attribute
with
  RelshipEnd : EClass :=
  BuildRelshipEnd :
    (*oid*) nat -> 
    (*name*) string -> RelshipEnd
.




(* StructuralFeature Accessors *)

  (** ERSchema *)

Definition ERSchemaOid (s : ERSchema) : nat :=
  match s with BuildERSchema oid _ _ _ => oid end.

Definition ERSchemaName (s : ERSchema) : string :=
  match s with BuildERSchema _ name _ _ => name end.

Definition ERSchemaEntities (s : ERSchema) : list Entity :=
  match s with BuildERSchema _ _ entities _ => entities end.

Definition ERSchemaRelships (s : ERSchema) : list Relship :=
  match s with BuildERSchema _ _ _ relships => relships end.

  (** Entity *)

Definition EntityOid (e : Entity) : nat :=
  match e with BuildEntity oid _ _ _ => oid end.

Definition EntityName (e : Entity) : string :=
  match e with BuildEntity _ name _ _ => name end.

Definition EntityAttrs (e : Entity) : list Attribute :=
  match e with BuildEntity _ _ attrs _ => attrs end.

Definition EntityEnds (e : Entity) : list RelshipEnd:=
  match e with BuildEntity _ _ _ ends => ends end.

  (** Relship *)

Definition RelshipOid (r : Relship) : nat :=
  match r with BuildRelship oid _ _ _ => oid end.

Definition RelshipName (r : Relship) : string :=
  match r with BuildRelship _ name _ _ => name end.

Definition RelshipAttrs (r : Relship) : list Attribute :=
  match r with BuildRelship _ _ attrs _ => attrs end.

Definition RelshipEnds (r : Relship) : list RelshipEnd :=
  match r with BuildRelship _ _ _ ends => ends end.

  (** Attribute *)

Definition AttributeOid (a : Attribute) : nat :=
  match a with BuildAttribute oid _ _ => oid end.

Definition AttributeName (a : Attribute) : string :=
  match a with BuildAttribute _ name _ => name end.

Definition AttributeIsKey (a : Attribute) : bool :=
  match a with BuildAttribute _ _ isKey => isKey end.
  (** RelshipEnd *)

Definition RelshipEndOid (ed : RelshipEnd) : nat :=
  match ed with BuildRelshipEnd oid _ => oid end.

Definition RelshipEndName (ed : RelshipEnd) : string :=
  match ed with BuildRelshipEnd _ name => name end.



(* Class Model *)



(* Properties *)



End ER.
