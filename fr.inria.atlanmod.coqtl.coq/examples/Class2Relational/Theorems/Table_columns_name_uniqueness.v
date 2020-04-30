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

(** missing coercison on model links *)
Definition ClassMetamodel_toELinkFromClassAttributes (cas :ClassAttributes) : ClassMetamodel_ELink :=
  (ClassMetamodel_BuildELink ClassAttributesEReference cas).
Coercion ClassMetamodel_toELinkFromClassAttributes : ClassAttributes >-> ClassMetamodel_ELink.

Definition RelationalMetamodel_toELinkFromTableColumns (tcs : TableColumns) : RelationalMetamodel_ELink :=
  (RelationalMetamodel_BuildELink TableColumnsReference tcs).
Coercion RelationalMetamodel_toELinkFromTableColumns : TableColumns >-> RelationalMetamodel_ELink.

(** potential helper to trigger coercison *)
Definition IIn (A: Type) (a: A) (l : list A) :=
  In a l.


Theorem Table_columns_name_uniqueness :
  forall (cm : ClassModel) (rm : RelationalModel), 
      (* transformation *) rm = execute Class2Relational cm ->
      (* precondition *) (forall (cas : ClassAttributes), IIn ClassMetamodel_ELink cas (allModelLinks cm) -> 
        forall (c: Class) (a1 a2: Attribute) (attrs: list Attribute), BuildClassAttributes c attrs = cas -> 
          In a1 attrs -> In a2 attrs -> a1 <> a2 ->
            (getAttributeName a1) <> (getAttributeName a2))  ->
      (* postcondition *) (forall (tcs : TableColumns), IIn RelationalMetamodel_ELink tcs (allModelLinks rm) -> 
        forall (t: Table) (col1 col2: Column) (cols: list Column), (BuildTableColumns t cols) = tcs ->
          In col1 cols -> In col2 cols -> col1 <> col2 ->
          (getColumnName col1) <> (getColumnName col2)) .
Proof. 
  (** Clean context *)
  intros cm rm tr pre.
  intros tcs Hintm t col1 col2 tcols.
  intros Hcols HinCol1 HinCol2 HcolEq.
  rewrite tr in Hintm.
  apply tr_execute_in_links in Hintm.
  destruct Hintm. rename x into sp.
  destruct H. rename x into tpl.
  destruct H. rename H into Hspincm.
  destruct H0. rename H into Happly.
  rename H0 into Htintpl.

  (** Unfolding theorem tr_applyPattern_in *)
  assert (exists tpl: list RelationalMetamodel_ELink, applyPattern Class2Relational cm sp = Some tpl /\ IIn RelationalMetamodel_ELink tcs tpl).
  { exists tpl. crush. }
  apply tr_applyPattern_in in H.
  destruct H. rename x into rl.
  destruct H. rename x into tpl1.
  destruct H. rename H into Hrl.
  destruct H0. rename H into Happly2. rename H0 into Hintpl1.  
  
  (** Unfolding theorem tr_matchPattern_in *)
  apply tr_matchPattern_in in Hrl.
  destruct Hrl. rename H into HrinTr. rename H0 into Hmatch.
Admitted.