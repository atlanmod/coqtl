Require Import List.

Require Import core.Model.

Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Require Import example.PersonModel.

Require Import String.

Require Import core.CoqTL.
Require Import core.utils.tPrint.

Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.
Require Import example.Class2Relational.
Require Import example.PersonModel.

(* Part I: transform objets:
   - Class to Table 
   - Attribute to Column
   - derived Attribute to nothing 
*)

Fixpoint objectsClassToRelational os :=
  match os with
  | nil => nil
  | ClassMetamodel_BuildEObject ClassEClass (BuildClass id name)::os1
    => (RelationalMetamodel_BuildEObject TableClass (BuildTable id name))::objectsClassToRelational os1
  | ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute id false name)::os1
    => RelationalMetamodel_BuildEObject ColumnClass (BuildColumn id name)::objectsClassToRelational os1
  | ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute id true name)::os1
    => objectsClassToRelational os1 
  end.

(* Part II: transform links:
   - (non derived) attributes in class become list of links from table to column
   - (non derived) attribute reference become reference from column to class
*)

Fixpoint classAttributesToTableColumnReference ats :=
  match ats with
  | nil => nil
  | BuildAttribute id false name::ats1 => BuildColumn id name::classAttributesToTableColumnReference ats1
  | BuildAttribute id true name::ats1 => classAttributesToTableColumnReference ats1
end.                                                     

Fixpoint linksClassToRelational ls :=
  match ls with
  | nil => nil
  | ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (BuildClass id name) ats) :: ls1
    => match classAttributesToTableColumnReference ats with
      | nil => linksClassToRelational ls1
      | es => RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns (BuildTable id name) es) :: linksClassToRelational ls1
      end  
  | ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute id false name) (BuildClass idC nameC)) :: ls1
    => RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference (BuildColumn id name) (BuildTable idC nameC)) :: linksClassToRelational ls1 
  | ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (BuildAttribute id true name) (BuildClass idC nameC)) :: ls1
    => linksClassToRelational ls1
  end.

(* model transformation *)

Definition transfoClassToRelational (m : ClassModel) := 
  BuildModel (objectsClassToRelational (allModelElements m))
             (linksClassToRelational (allModelLinks m)). 


Compute (transfoClassToRelational PersonModel).
(*
 = BuildModel
         (RelationalMetamodel_BuildEObject TableClass (BuildTable 0 "Person")
          :: RelationalMetamodel_BuildEObject ColumnClass (BuildColumn 1 "father") :: nil)
         (RelationalMetamodel_BuildELink TableColumnsReference
            (BuildTableColumns (BuildTable 0 "Person") (BuildColumn 1 "father" :: nil))
          :: RelationalMetamodel_BuildELink ColumnReferenceReference
               (BuildColumnReference (BuildColumn 1 "father") (BuildTable 0 "Person")) :: nil)
     : Model RelationalMetamodel_EObject RelationalMetamodel_ELink
*)

(* massimo / cheng reference *)

Compute (execute Class2Relational PersonModel).

(*
 = BuildModel
         (RelationalMetamodel_BuildEObject TableClass (BuildTable 0 "Person")
          :: RelationalMetamodel_BuildEObject ColumnClass (BuildColumn 1 "father") :: nil)
         (RelationalMetamodel_BuildELink TableColumnsReference
            (BuildTableColumns (BuildTable 0 "Person") (BuildColumn 1 "father" :: nil))
          :: RelationalMetamodel_BuildELink ColumnReferenceReference
               (BuildColumnReference (BuildColumn 1 "father") (BuildTable 0 "Person")) :: nil)
     : TargetModel RelationalMetamodel_EObject RelationalMetamodel_ELink
*)

(* theorem and proof *)

(* ???
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  
*)

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import example.Class2Relational.
Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = transfoClassToRelational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.