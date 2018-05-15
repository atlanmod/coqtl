Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.

Require Import core.utils.Utils_Top.
Require Import core.CoqTL.

Require Import Coq.Logic.Eqdep_dec.

(* Base types *)

Inductive
  Table : Set :=
  BuildTable :
    nat ->
    string -> Table.

Inductive
  Column : Set :=
  BuildColumn :
    nat ->
    string -> Column.

Inductive  
  TableColumns : Set :=
  BuildTableColumns :  Table -> list Column -> TableColumns.

Inductive  
  ColumnReference : Set :=
  BuildColumnReference : Column -> Table -> ColumnReference.

(* Accessors *)

Definition getTableId (t : Table) : nat :=
  match t with BuildTable id _ => id end.

Definition getTableName (t : Table) : string :=
  match t with BuildTable _ n => n end.

Definition getColumnId (c : Column) : nat :=
  match c with BuildColumn id _ => id end.

Definition getColumnName (c : Column) : string :=
  match c with BuildColumn _ n => n end.
  
Definition beq_Table (t1 : Table) (t2: Table) : bool :=
  beq_nat (getTableId t1) (getTableId t2) && beq_string (getTableName t1) (getTableName t2).

Definition beq_Column (c1 : Column) (c2 : Column) : bool :=
  beq_nat (getColumnId c1) (getColumnId c2) && beq_string (getColumnName c1) (getColumnName c2).

Lemma lem_beq_Table_id:
 forall (a1 a2: Table),
   beq_Table a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Table in H.
unfold "&&" in H.
destruct (getTableId a1 =? getTableId a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

Lemma lem_beq_Table_refl:
 forall (a: Table),
   beq_Table a a = true.
Proof.
intros.
destruct a.
unfold beq_Table.
simpl.
assert (true = PeanoNat.Nat.eqb n n). { apply beq_nat_refl. }
rewrite <- H.
assert (beq_string s s = true). { apply lem_beq_string_id. }
rewrite H0.
simpl.
auto.
Qed.

Lemma lem_beq_Column_refl : 
 forall (c: Column),
   beq_Column c c = true.
Proof.
intros.
destruct c.
unfold beq_Column.
simpl.
assert (beq_nat n n = true). {symmetry. apply beq_nat_refl. }
assert (beq_string s s = true). {apply lem_beq_string_id. }
rewrite H,H0.
simpl.
auto.
Qed.


Lemma lem_beq_Column_id:
 forall (a1 a2: Column),
   beq_Column a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Column in H.
unfold "&&" in H.
destruct (getColumnId a1 =? getColumnId a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

(* Meta-types *)

Inductive RelationalMetamodel_EClass : Set :=
  TableClass | ColumnClass.

Definition RelationalMetamodel_getTypeByEClass (type : RelationalMetamodel_EClass) : Set :=
  match type with
  | TableClass => Table
  | ColumnClass => Column
  end.

Inductive RelationalMetamodel_EReference : Set :=
  TableColumnsReference | ColumnReferenceReference.

Definition RelationalMetamodel_getTypeByEReference (type : RelationalMetamodel_EReference) : Set :=
  match type with
  | TableColumnsReference => TableColumns
  | ColumnReferenceReference => ColumnReference
  end.

(* Generic types *)

Inductive RelationalMetamodel_EObject : Set :=
| RelationalMetamodel_BuildEObject : forall (c:RelationalMetamodel_EClass), (RelationalMetamodel_getTypeByEClass c) -> RelationalMetamodel_EObject.

Inductive RelationalMetamodel_ELink : Set :=
| RelationalMetamodel_BuildELink : forall (c:RelationalMetamodel_EReference), (RelationalMetamodel_getTypeByEReference c) -> RelationalMetamodel_ELink.



(* Reflective functions *)

Lemma RelationalMetamodel_eqEClass_dec : forall (c1:RelationalMetamodel_EClass) (c2:RelationalMetamodel_EClass), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma RelationalMetamodel_eqEReference_dec : forall (c1:RelationalMetamodel_EReference) (c2:RelationalMetamodel_EReference), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition RelationalMetamodel_getEClass (c : RelationalMetamodel_EObject) : RelationalMetamodel_EClass :=
  match c with
  | (RelationalMetamodel_BuildEObject t _) => t
  end.

Definition RelationalMetamodel_getEReference (c : RelationalMetamodel_ELink) : RelationalMetamodel_EReference :=
  match c with
  | (RelationalMetamodel_BuildELink t _) => t
  end.

Definition RelationalMetamodel_instanceOfEClass (cmc: RelationalMetamodel_EClass) (c : RelationalMetamodel_EObject): bool :=
  if RelationalMetamodel_eqEClass_dec (RelationalMetamodel_getEClass c) cmc then true else false.

Definition RelationalMetamodel_instanceOfEReference (cmr: RelationalMetamodel_EReference) (c : RelationalMetamodel_ELink): bool :=
  if RelationalMetamodel_eqEReference_dec (RelationalMetamodel_getEReference c) cmr then true else false.

Definition RelationalMetamodel_EClassAttributeTypes (c: RelationalMetamodel_EClass): Set :=
  match c with
  | TableClass => (nat * string)
  | ColumnClass => (nat * string)
  end.

Definition BuildRelationalMetamodel_EClassElement (t : RelationalMetamodel_EClass) : (RelationalMetamodel_EClassAttributeTypes t) -> RelationalMetamodel_EObject :=
  match t with
  | TableClass => (fun (p: nat * string) => (RelationalMetamodel_BuildEObject TableClass (BuildTable (fst p) (snd p))))
  | ColumnClass => (fun (p: nat * string) => (RelationalMetamodel_BuildEObject ColumnClass (BuildColumn (fst p) (snd p))))
  end.

Definition RelationalMetamodel_EReferenceRoleTypes (c: RelationalMetamodel_EReference): Set :=
  match c with
  | TableColumnsReference => (Table * list Column)
  | ColumnReferenceReference => (Column * Table)
  end.

Definition BuildRelationalMetamodel_EReferenceLink (t : RelationalMetamodel_EReference) : (RelationalMetamodel_EReferenceRoleTypes t) -> RelationalMetamodel_ELink :=
  match t with
  | TableColumnsReference => (fun (p: Table * list Column) => (RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns (fst p) (snd p))))
  | ColumnReferenceReference => (fun (p: Column * Table) => (RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference (fst p) (snd p))))
  end.

Definition toRelationalMetamodel_EClass (t : RelationalMetamodel_EClass) (c : RelationalMetamodel_EObject) : option (RelationalMetamodel_getTypeByEClass t) :=
  match c with
| RelationalMetamodel_BuildEObject c0 d =>
    let s := RelationalMetamodel_eqEClass_dec c0 t in
    match s with
    | left e => match e with
                     eq_refl => Some d
               end
    | right _ => None
    end
  end.

(*Proof.
  destruct c.
  destruct (RelationalMetamodel_eqEClass_dec t r).
  - rewrite <- e in d.
    exact (Some d).
  - exact None.
Defined.*)

Theorem toRelationalMetamodel_EClass_inv :
  forall (t : RelationalMetamodel_EClass) (c : RelationalMetamodel_EObject) (c': RelationalMetamodel_getTypeByEClass t),
    toRelationalMetamodel_EClass t c = Some c' ->
    c = (RelationalMetamodel_BuildEObject t c').
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct (RelationalMetamodel_eqEClass_dec c t).
  - destruct e. inversion H. reflexivity.
  - inversion H.
Qed.

Definition toRelationalMetamodel_EReference (t : RelationalMetamodel_EReference) (c : RelationalMetamodel_ELink) : option (RelationalMetamodel_getTypeByEReference t).
Proof.
  destruct c.
  destruct (RelationalMetamodel_eqEReference_dec t c).
  - rewrite <- e in r.
    exact (Some r).
  - exact None.
Defined.

(* Generic functions *)

Definition RelationalMetamodel_toEObjectFromTable (t :Table) : RelationalMetamodel_EObject :=
  (RelationalMetamodel_BuildEObject TableClass t).
Coercion RelationalMetamodel_toEObjectFromTable : Table >-> RelationalMetamodel_EObject.
Definition RelationalMetamodel_toEObject (c : RelationalMetamodel_EObject) : RelationalMetamodel_EObject := c.

Definition RelationalMetamodel_toEObjectFromColumn (c :Column) : RelationalMetamodel_EObject :=
  (RelationalMetamodel_BuildEObject ColumnClass c).
Coercion RelationalMetamodel_toEObjectFromColumn : Column >-> RelationalMetamodel_EObject.
Definition RelationalMetamodel_toELink (c : RelationalMetamodel_ELink) : RelationalMetamodel_ELink := c.

Definition RelationalMetamodel_toEObjectOfEClass (t: RelationalMetamodel_EClass) (e: RelationalMetamodel_getTypeByEClass t) : RelationalMetamodel_EObject:=
  (RelationalMetamodel_BuildEObject t e).



Definition RelationalMetamodel_getId (r : RelationalMetamodel_EObject) : nat :=
  match r with
  | (RelationalMetamodel_BuildEObject TableClass c) => getTableId c
  | (RelationalMetamodel_BuildEObject ColumnClass a) => getColumnId a
  end.



(*Definition allTables (m : RelationalModel) : list Table :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_EClass TableClass) l) end.

Definition allColumns (m : RelationalModel) : list Column :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_EClass ColumnClass) l) end.*)

Fixpoint getTableColumnsOnLinks (t : Table) (l : list RelationalMetamodel_ELink) : option (list Column) :=
  match l with
  | (RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns tab c)) :: l1 => if beq_Table tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table) (m : Model RelationalMetamodel_EObject RelationalMetamodel_ELink) : option (list Column) :=
  match m with
    (BuildModel rs ls) => getTableColumnsOnLinks t ls
  end.

Fixpoint getColumnReferenceOnLinks (c : Column) (l : list RelationalMetamodel_ELink) : option Table :=
  match l with
  | (RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference col t)) :: l1 => if beq_Column col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column) (m : Model RelationalMetamodel_EObject RelationalMetamodel_ELink) : option Table :=
  match m with
    (BuildModel rs ls) => getColumnReferenceOnLinks c ls
  end.

Definition bottomRelationalMetamodel_EClass (c: RelationalMetamodel_EClass) : (RelationalMetamodel_getTypeByEClass c) :=
  match c with
  | TableClass => (BuildTable 0 "")
  | ColumnClass => (BuildColumn 0 "")
  end.

Lemma rel_invert : 
  forall (t: RelationalMetamodel_EClass) (t1 t2: RelationalMetamodel_getTypeByEClass t), RelationalMetamodel_BuildEObject t t1 = RelationalMetamodel_BuildEObject t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqEClass_dec.
Qed.

Lemma rel_elink_invert : 
  forall (t: RelationalMetamodel_EReference) (t1 t2: RelationalMetamodel_getTypeByEReference t), RelationalMetamodel_BuildELink t t1 = RelationalMetamodel_BuildELink t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqEReference_dec.
Qed.

Instance RelationalMetamodel : Metamodel RelationalMetamodel_EObject RelationalMetamodel_ELink RelationalMetamodel_EClass RelationalMetamodel_EReference :=
  {
    denoteModelClass := RelationalMetamodel_getTypeByEClass;
    denoteModelReference := RelationalMetamodel_getTypeByEReference;
    toModelClass := toRelationalMetamodel_EClass;
    toModelReference := toRelationalMetamodel_EReference;
    toModelElement := RelationalMetamodel_toEObjectOfEClass;
    bottomModelClass := bottomRelationalMetamodel_EClass;

    (* Theorems *)
    eqModelClass_dec := RelationalMetamodel_eqEClass_dec;
    eqModelReference_dec := RelationalMetamodel_eqEReference_dec;

    (* Constructors *)
    BuildModelElement := RelationalMetamodel_BuildEObject;
    BuildModelLink := RelationalMetamodel_BuildELink;
  }.
  

  


Definition RelationalModel := Model RelationalMetamodel_EObject RelationalMetamodel_ELink.

