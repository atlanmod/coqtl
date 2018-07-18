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

(* a simplified version of the problem *)

(* class | attribute | derived attribute *)
Inductive Input : Set := | I0 : nat -> Input | I1 | I2.
(* table | column *)
Inductive Output : Set := | O0 : nat -> Output | O1.

(* transformation framework *)
Fixpoint tranfo is1 :=
  match is1 with
  | nil => nil
  | I0 n::is2 => O0 n::tranfo is2
  | I1::is2 => O1::tranfo is2
  | I2::is2 => tranfo is2
  end.


Theorem Remi1 :
  forall (is1 : list Input), 
    forall (n : nat),
      In (O0 n) (tranfo is1)
      -> exists (i1 : Input),
        (O0 n)::nil = tranfo (i1::nil) /\ In i1 is1 .
Proof.
  intros inputList.
  induction inputList.
  * intros n HInOutput.
    inversion HInOutput.
  * intros n HInOutput.
    destruct a.
    ** simpl in HInOutput.
       destruct HInOutput.
       *** inversion H.
           subst.
           exists (I0 n).
           simpl.    
           auto. 
       *** exists (I0 n).
           simpl.
           split.
           **** auto.
           **** right.
                apply IHinputList in H.
                destruct H as [i1].
                destruct H.
                inversion H.
                destruct i1.
                ***** inversion H2.
                      auto.
                ***** inversion H2.
                ***** inversion H2.
    ** simpl in HInOutput.
       destruct HInOutput.
       *** inversion H.
       *** apply IHinputList in H.
           destruct H.
           destruct H.
           simpl in H.
           destruct x.
           **** inversion H.
                subst.
                exists (I0 n0).
                simpl.
                auto.
           **** inversion H.
           **** inversion H.
    ** simpl in HInOutput.
       apply IHinputList in HInOutput.
       destruct HInOutput.       
       simpl in H.
       destruct H.
       destruct x.
       *** inversion H.
           subst.
           exists (I0 n0).
           simpl.
           auto.
       *** inversion H.
       *** inversion H.
Defined.
           
(* remi adhoc/specialized transformation *)
  
(* Part I: transform objets:
   - Class to Table 
   - Attribute to Column
   - derived Attribute to nothing 
*)

(* specialized transformation *)

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
  Build_Model (objectsClassToRelational (@allModelElements _ _ m))
             (linksClassToRelational (@allModelLinks _ _ m)). 

(* test remi *)

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

(* test massimo / cheng reference *)

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

(* Print objectsClassToRelational. *)

Theorem Remi2 :
  forall (os : list ClassMetamodel_EObject), 
    forall (t1 : RelationalMetamodel_EObject),
      In t1 (objectsClassToRelational os)
      -> exists (c1 : ClassMetamodel_EObject),
        t1::nil = objectsClassToRelational (c1::nil) /\ In c1 os.
Proof. 
  intros os.
  induction os.
  * (* nil *)
    intros t1 Ht1In.
    inversion Ht1In.
  * (* cons *)
    intros t1 Ht1In.
    destruct a.
    destruct c.
    ** (* class *)
      destruct c0 as [n s].
      destruct Ht1In as [ H | H ]. 
      *** (* t1 in head *)
        exists (ClassMetamodel_BuildEObject ClassEClass (BuildClass n s)). 
        subst.
        simpl.
        auto.
      *** (* t1 in tail *)
        apply IHos in H.
        destruct H as [x H].
        destruct x as [c c0].
        destruct c.
        **** (* class *)
          destruct c0 as [n0 s0].             
          exists (ClassMetamodel_BuildEObject ClassEClass (BuildClass n0 s0)). 
          destruct H as [H H0]. 
          simpl.
          auto.
        **** (* attribute *)
          destruct c0 as [n0 b s0].             
          exists (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute n0 b s0)).
          destruct H as [H H0].
          simpl.
          auto.
    ** (* attribute *)                   
      destruct c0 as [n b s].
      destruct b.
      *** (* b is true *)
        apply IHos in Ht1In.
        inversion Ht1In as [x H].
        destruct x as [c c0].
        destruct c.
        ****
          destruct c0 as [n0 s0].
          exists (ClassMetamodel_BuildEObject ClassEClass (BuildClass n0 s0)).
          destruct H as [H H0].
          split.
          *****
            exact H.
          *****
            right.
            exact H0.
        ****
          exists (ClassMetamodel_BuildEObject AttributeEClass c0).
          destruct H as [H H0].
          split.
          *****
            exact H.
          *****
            right.
            exact H0.
      *** (* b is false *) 
        inversion Ht1In as [H | H].
        **** (* head *)
          exists (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute n false s)).
          subst.
          simpl.
          auto.
        **** (* tail *)
          apply IHos in H.
          destruct H as [x H].
          destruct H as [H H0].
          destruct x as [c c0]. 
          destruct c.
          ***** (* ClassEClass *)
            destruct c0 as [n0 s0].
            exists (ClassMetamodel_BuildEObject ClassEClass (BuildClass n0 s0)).
            simpl.
            auto.
         ***** (* AttributeEClass *)
           destruct c0.
           exists (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute n0 b s0)).
           simpl.
           auto.
Defined.
         
Check (unfold Remi2).