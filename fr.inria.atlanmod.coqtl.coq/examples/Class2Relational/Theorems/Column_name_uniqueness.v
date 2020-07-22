(**
 CoqTL user theorem: Column_name_uniqueness
 Def: if all attributes of the same class have unique names,
      then the generated columns of the same table
      have unique names.
 **)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Column_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
    (* transformation *)
    rm = execute Class2Relational cm ->
    (* precondition *)
    (forall (at1: Attribute) (at2: Attribute) (cl: Class) (ats: list Attribute),
        In (ClassMetamodel_toObject AttributeClass at1) (allModelElements cm) ->
        In (ClassMetamodel_toObject AttributeClass at2) (allModelElements cm) ->
        In (ClassMetamodel_toObject ClassClass cl) (allModelElements cm) ->
        getClassAttributes cl cm = Some ats ->
        In at1 ats ->
        In at2 ats ->
        at1 <> at2 ->
        getAttributeName at1 <> getAttributeName at2) ->
    (* postcondition *)
    (forall (co1: Column) (co2: Column) (ta: Table) (cos: list Column),
        In (RelationalMetamodel_toObject ColumnClass co1) (allModelElements rm) ->
        In (RelationalMetamodel_toObject ColumnClass co2) (allModelElements rm) ->
        In (RelationalMetamodel_toObject TableClass ta) (allModelElements rm) ->
        getTableColumns ta rm = Some cos ->
        In co1 cos ->
        In co2 cos ->
        co1 <> co2 ->
        getColumnName co1 <> getColumnName co2).
Proof.
    intros.
    rewrite H in H1, H2, H3.
    rewrite tr_execute_in_elements in H1, H2, H3.
    do 2 destruct H1, H2, H3.
    destruct x, x0, x1.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - contradiction.
    - (* [x::_] [y::_] [z::_] *) 
      destruct x, x0, x1.
      + (* [x] [y] [z] *)
        do 2 destruct c, c0, c1.
        * destruct c2. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct c2. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct c2. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct c2. simpl in H8. destruct H8. inversion H8. contradiction.
        * destruct c3. simpl in H9. destruct H9. inversion H9. contradiction.
        * destruct c3. simpl in H9. destruct H9. inversion H9. contradiction.
        * (* [a] [a] [c] *)
Admitted.
