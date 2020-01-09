Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Definition IIn (A: Type) (a: A) (l : list A) :=
  In a l.

Theorem Table_columns_name_uniqueness :
  forall (cm : ClassModel) (rm : RelationalModel), 
      (* transformation *) rm = execute Class2Relational cm ->
      (* precondition *) (forall (c1 : Class), IIn ClassMetamodel_EObject c1 (allModelElements cm) -> 
        forall (a1 a2: Attribute) (attrs: list Attribute), (getClassAttributes c1 cm) = Some attrs -> 
          In a1 attrs -> In a2 attrs -> a1 <> a2 ->
            (getAttributeName a1) <> (getAttributeName a2))  ->
      (* postcondition *) (forall (t1 : Table), IIn RelationalMetamodel_EObject t1 (allModelElements rm) -> 
        forall (col1 col2: Column) (cols: list Column), (getTableColumns t1 rm) = Some cols ->
          In col1 cols -> In col2 cols -> col1 <> col2 ->
          (getColumnName col1) <> (getColumnName col2)) .
Proof. 
  intros cm rm tr pre t Hint col1 col2 tcols.
  intros Hcols HinCol1 HinCol2 HcolEq.