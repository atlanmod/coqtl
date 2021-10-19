Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import core.EqDec.
Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.modeling.ModelingMetamodel.
Require Import core.Model.

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

Definition maybeBuildColumnReference (c: Column) (t: option Table) : option ColumnReference :=
  match c, t with
  | c', Some t' => Some (BuildColumnReference c' t')
  | _, _ => None
  end.  

Definition maybeBuildTableColumns (t: Table) (c: option (list Column)) : option TableColumns :=
  match t, c with
  | t', Some c' => Some (BuildTableColumns t' c')
  | _, _ => None
  end.  

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

Inductive RelationalMetamodel_Class : Set :=
  TableClass | ColumnClass.

Definition RelationalMetamodel_getTypeByClass (type : RelationalMetamodel_Class) : Set :=
  match type with
  | TableClass => Table
  | ColumnClass => Column
  end.

Inductive RelationalMetamodel_Reference : Set :=
  TableColumnsReference | ColumnReferenceReference.

Definition RelationalMetamodel_getTypeByReference (type : RelationalMetamodel_Reference) : Set :=
  match type with
  | TableColumnsReference => TableColumns
  | ColumnReferenceReference => ColumnReference
  end.

(* Generic types *)

Inductive RelationalMetamodel_Object : Set :=
| RelationalMetamodel_BuildObject : forall (c:RelationalMetamodel_Class), (RelationalMetamodel_getTypeByClass c) -> RelationalMetamodel_Object.

Definition beq_RelationalMetamodel_Object (c1 : RelationalMetamodel_Object) (c2 : RelationalMetamodel_Object) : bool :=
  match c1, c2 with
  | RelationalMetamodel_BuildObject TableClass o1, RelationalMetamodel_BuildObject TableClass o2 => beq_Table o1 o2
  | RelationalMetamodel_BuildObject ColumnClass o1, RelationalMetamodel_BuildObject ColumnClass o2 => beq_Column o1 o2
  | _, _ => false
  end.

Inductive RelationalMetamodel_Link : Set :=
| RelationalMetamodel_BuildLink : forall (c:RelationalMetamodel_Reference), (RelationalMetamodel_getTypeByReference c) -> RelationalMetamodel_Link.



(* Reflective functions *)

Lemma RelationalMetamodel_eqClass_dec : forall (c1:RelationalMetamodel_Class) (c2:RelationalMetamodel_Class), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma RelationalMetamodel_eqReference_dec : forall (c1:RelationalMetamodel_Reference) (c2:RelationalMetamodel_Reference), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition RelationalMetamodel_getClass (c : RelationalMetamodel_Object) : RelationalMetamodel_Class :=
  match c with
  | (RelationalMetamodel_BuildObject t _) => t
  end.

Definition RelationalMetamodel_getReference (c : RelationalMetamodel_Link) : RelationalMetamodel_Reference :=
  match c with
  | (RelationalMetamodel_BuildLink t _) => t
  end.

Definition RelationalMetamodel_instanceOfClass (cmc: RelationalMetamodel_Class) (c : RelationalMetamodel_Object): bool :=
  if RelationalMetamodel_eqClass_dec (RelationalMetamodel_getClass c) cmc then true else false.

Definition RelationalMetamodel_instanceOfReference (cmr: RelationalMetamodel_Reference) (c : RelationalMetamodel_Link): bool :=
  if RelationalMetamodel_eqReference_dec (RelationalMetamodel_getReference c) cmr then true else false.

Definition RelationalMetamodel_ClassAttributeTypes (c: RelationalMetamodel_Class): Set :=
  match c with
  | TableClass => (nat * string)
  | ColumnClass => (nat * string)
  end.

Definition BuildRelationalMetamodel_ClassElement (t : RelationalMetamodel_Class) : (RelationalMetamodel_ClassAttributeTypes t) -> RelationalMetamodel_Object :=
  match t with
  | TableClass => (fun (p: nat * string) => (RelationalMetamodel_BuildObject TableClass (BuildTable (fst p) (snd p))))
  | ColumnClass => (fun (p: nat * string) => (RelationalMetamodel_BuildObject ColumnClass (BuildColumn (fst p) (snd p))))
  end.

Definition RelationalMetamodel_ReferenceRoleTypes (c: RelationalMetamodel_Reference): Set :=
  match c with
  | TableColumnsReference => (Table * list Column)
  | ColumnReferenceReference => (Column * Table)
  end.

Definition BuildRelationalMetamodel_ReferenceLink (t : RelationalMetamodel_Reference) : (RelationalMetamodel_ReferenceRoleTypes t) -> RelationalMetamodel_Link :=
  match t with
  | TableColumnsReference => (fun (p: Table * list Column) => (RelationalMetamodel_BuildLink TableColumnsReference (BuildTableColumns (fst p) (snd p))))
  | ColumnReferenceReference => (fun (p: Column * Table) => (RelationalMetamodel_BuildLink ColumnReferenceReference (BuildColumnReference (fst p) (snd p))))
  end.

Definition toRelationalMetamodel_Class (t : RelationalMetamodel_Class) (c : RelationalMetamodel_Object) : option (RelationalMetamodel_getTypeByClass t) :=
  match c with
| RelationalMetamodel_BuildObject c0 d =>
    let s := RelationalMetamodel_eqClass_dec c0 t in
    match s with
    | left e => match e with
                     eq_refl => Some d
               end
    | right _ => None
    end
  end.

(*Proof.
  destruct c.
  destruct (RelationalMetamodel_eqClass_dec t r).
  - rewrite <- e in d.
    exact (Some d).
  - exact None.
Defined.*)

Theorem toRelationalMetamodel_Class_inv :
  forall (t : RelationalMetamodel_Class) (c : RelationalMetamodel_Object) (c': RelationalMetamodel_getTypeByClass t),
    toRelationalMetamodel_Class t c = Some c' ->
    c = (RelationalMetamodel_BuildObject t c').
Proof.
  intros.
  destruct c.
  simpl in H.
  destruct (RelationalMetamodel_eqClass_dec c t).
  - destruct e. inversion H. reflexivity.
  - inversion H.
Qed.

Definition toRelationalMetamodel_Reference (t : RelationalMetamodel_Reference) (c : RelationalMetamodel_Link) : option (RelationalMetamodel_getTypeByReference t).
Proof.
  destruct c.
  destruct (RelationalMetamodel_eqReference_dec t c).
  - rewrite <- e in r.
    exact (Some r).
  - exact None.
Defined.

(* Generic functions *)

Definition RelationalMetamodel_toObjectFromTable (t :Table) : RelationalMetamodel_Object :=
  (RelationalMetamodel_BuildObject TableClass t).

Definition RelationalMetamodel_toObjectFromColumn (c :Column) : RelationalMetamodel_Object :=
  (RelationalMetamodel_BuildObject ColumnClass c).

Definition RelationalMetamodel_toObject (t: RelationalMetamodel_Class) (e: RelationalMetamodel_getTypeByClass t) : RelationalMetamodel_Object:=
  (RelationalMetamodel_BuildObject t e).

Definition RelationalMetamodel_toLink (t: RelationalMetamodel_Reference) (e: RelationalMetamodel_getTypeByReference t) : RelationalMetamodel_Link :=
  (RelationalMetamodel_BuildLink t e).

Definition RelationalMetamodel_getId (r : RelationalMetamodel_Object) : nat :=
  match r with
  | (RelationalMetamodel_BuildObject TableClass c) => getTableId c
  | (RelationalMetamodel_BuildObject ColumnClass a) => getColumnId a
  end.

Definition RelationalMetamodel_getName (r : RelationalMetamodel_Object) : string :=
  match r with
  | (RelationalMetamodel_BuildObject TableClass c) => getTableName c
  | (RelationalMetamodel_BuildObject ColumnClass a) => getColumnName a
  end.

(*Definition allTables (m : RelationalModel) : list Table :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class TableClass) l) end.

Definition allColumns (m : RelationalModel) : list Column :=
  match m with BuildRelationalModel l _  => optionList2List (map (toRelationalMetamodel_Class ColumnClass) l) end.*)

Fixpoint getTableColumnsOnLinks (t : Table) (l : list RelationalMetamodel_Link) : option (list Column) :=
  match l with
  | (RelationalMetamodel_BuildLink TableColumnsReference (BuildTableColumns tab c)) :: l1 => if beq_Table tab t then Some c else getTableColumnsOnLinks t l1
  | _ :: l1 => getTableColumnsOnLinks t l1
  | nil => None
  end.

Definition getTableColumns (t : Table) (m : Model RelationalMetamodel_Object RelationalMetamodel_Link) : option (list Column) :=
getTableColumnsOnLinks t (allModelLinks m).

Fixpoint getColumnReferenceOnLinks (c : Column) (l : list RelationalMetamodel_Link) : option Table :=
  match l with
  | (RelationalMetamodel_BuildLink ColumnReferenceReference (BuildColumnReference col t)) :: l1 => if beq_Column col c then Some t else getColumnReferenceOnLinks c l1
  | _ :: l1 => getColumnReferenceOnLinks c l1
  | nil => None
  end.

Definition getColumnReference (c : Column) (m : Model RelationalMetamodel_Object RelationalMetamodel_Link) : option Table := getColumnReferenceOnLinks c (allModelLinks m).

Definition bottomRelationalMetamodel_Class (c: RelationalMetamodel_Class) : (RelationalMetamodel_getTypeByClass c) :=
  match c with
  | TableClass => (BuildTable 0 "")
  | ColumnClass => (BuildColumn 0 "")
  end.

Lemma rel_invert : 
  forall (t: RelationalMetamodel_Class) (t1 t2: RelationalMetamodel_getTypeByClass t), RelationalMetamodel_BuildObject t t1 = RelationalMetamodel_BuildObject t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqClass_dec.
Qed.

Lemma rel_elink_invert : 
  forall (t: RelationalMetamodel_Reference) (t1 t2: RelationalMetamodel_getTypeByReference t), RelationalMetamodel_BuildLink t t1 = RelationalMetamodel_BuildLink t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqReference_dec.
Qed.

  Instance RelationalElementSum : Sum RelationalMetamodel_Object RelationalMetamodel_Class :=
  {
    denoteSubType := RelationalMetamodel_getTypeByClass;
    toSubType := toRelationalMetamodel_Class;
    toSumType := RelationalMetamodel_toObject;
  }.
  
  (* TODO *)
  Definition beq_RelationalMetamodel_Link (c1 : RelationalMetamodel_Link) (c2 : RelationalMetamodel_Link) : bool := true.
  
  Instance RelationalMetamodel_EqDec : EqDec RelationalMetamodel_Object := {
    eq_b := beq_RelationalMetamodel_Object;
  }.


  Instance RelationalLinkSum : Sum RelationalMetamodel_Link RelationalMetamodel_Reference :=
  {
    denoteSubType := RelationalMetamodel_getTypeByReference;
    toSubType := toRelationalMetamodel_Reference;
    toSumType := RelationalMetamodel_toLink;
  }.
  
  Instance RelationalM : Metamodel :=
  {
    ModelElement := RelationalMetamodel_Object;
    ModelLink := RelationalMetamodel_Link;
  }.

  Instance RelationalMetamodel : ModelingMetamodel RelationalM :=
  { 
      elements := RelationalElementSum;
      links := RelationalLinkSum;
  }.

Definition RelationalModel := Model RelationalMetamodel_Object RelationalMetamodel_Link.

