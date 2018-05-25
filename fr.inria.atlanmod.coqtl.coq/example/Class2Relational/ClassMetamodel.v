Require Import Bool.
Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Omega.


Require Import core.utils.tTop.
Require Import core.Metamodel.
Require Import core.Model.

(* Base types *)

Inductive Class : Set :=
    BuildClass :
      (* id *) nat ->
      (* name *) string -> Class.

Inductive Attribute : Set :=
    BuildAttribute :
      (* id *) nat ->
      (* derived *) bool ->
      (* name *) string -> Attribute.

Inductive ClassAttributes : Set :=
    BuildClassAttributes:
      Class ->
      list Attribute -> ClassAttributes.

Inductive AttributeType : Set :=
    BuildAttributeType:
      Attribute ->
      Class -> AttributeType.

(* Accessors *)

Definition getClassId (c : Class) : nat :=
  match c with BuildClass id _ => id end.

Definition getClassName (c : Class) : string :=
  match c with BuildClass _ n => n end.

Definition getAttributeId (a : Attribute) : nat :=
  match a with BuildAttribute id _ _ => id end.

Definition getAttributeName (a : Attribute) : string :=
  match a with BuildAttribute _ _ n => n end.

Definition getAttributeDerived (a : Attribute) : bool :=
  match a with BuildAttribute _ n _ => n end.

Definition beq_Class (c1 : Class) (c2 : Class) : bool :=
  beq_nat (getClassId c1) (getClassId c2) && beq_string (getClassName c1) (getClassName c2).

Definition beq_Attribute (a1 : Attribute) (a2 : Attribute) : bool :=
  beq_nat (getAttributeId a1) (getAttributeId a2) && eqb (getAttributeDerived a1) (getAttributeDerived a2) && beq_string (getAttributeName a1) (getAttributeName a2).

Lemma lem_beq_Class_id:
 forall (a1 a2: Class),
   beq_Class a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Class in H.
unfold "&&" in H.
destruct (getClassId a1 =? getClassId a2) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (beq_nat_true) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1,H.
  auto.
- congruence.
Qed.

Lemma lem_beq_Attribute_id:
 forall (a1 a2: Attribute),
   beq_Attribute a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Attribute in H.
unfold "&&" in H.
destruct (getAttributeId a1 =? getAttributeId a2) eqn: ca1.
- destruct (eqb (getAttributeDerived a1) (getAttributeDerived a2)) eqn: ca2.
  + apply (lem_beq_string_eq2) in H.
    apply (beq_nat_true) in ca1.
    apply (eqb_prop) in ca2.
    destruct a1,a2.
    simpl in ca1,ca2, H.
    rewrite ca1,ca2,H.
    auto.
  + congruence. 
- congruence.
Qed.



(* Meta-types *)

Inductive ClassMetamodel_EClass : Set :=
  ClassEClass | AttributeEClass.

Definition ClassMetamodel_getTypeByEClass (type : ClassMetamodel_EClass) : Set :=
  match type with
  | ClassEClass => Class
  | AttributeEClass => Attribute
  end.

Definition ClassMetamodel_getEAttributeTypesByEClass (c: ClassMetamodel_EClass): Set :=
  match c with
  | ClassEClass => (nat * string)
  | AttributeEClass => (nat * bool * string)
  end.

Inductive ClassMetamodel_EReference : Set :=
  ClassAttributesEReference | AttributeTypeEReference.

Definition ClassMetamodel_getTypeByEReference (type : ClassMetamodel_EReference) : Set :=
  match type with
  | ClassAttributesEReference => ClassAttributes
  | AttributeTypeEReference => AttributeType
  end.

Definition ClassMetamodel_getERoleTypesByEReference (c: ClassMetamodel_EReference): Set :=
  match c with
  | ClassAttributesEReference => (Class * list Attribute)
  | AttributeTypeEReference => (Attribute * Class)
  end.


(* Generic types *)

Inductive ClassMetamodel_EObject : Set :=
| ClassMetamodel_BuildEObject : forall (c:ClassMetamodel_EClass), (ClassMetamodel_getTypeByEClass c) -> ClassMetamodel_EObject.

Inductive ClassMetamodel_ELink : Set :=
| ClassMetamodel_BuildELink : forall (c:ClassMetamodel_EReference), (ClassMetamodel_getTypeByEReference c) -> ClassMetamodel_ELink.

(* Reflective functions *)

Lemma ClassMetamodel_eqEClass_dec : forall (c1:ClassMetamodel_EClass) (c2:ClassMetamodel_EClass), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Lemma ClassMetamodel_eqEReference_dec : forall (c1:ClassMetamodel_EReference) (c2:ClassMetamodel_EReference), { c1 = c2 } + { c1 <> c2 }.
Proof. repeat decide equality. Defined.

Definition ClassMetamodel_getEClass (c : ClassMetamodel_EObject) : ClassMetamodel_EClass :=
   match c with
  | (ClassMetamodel_BuildEObject c _) => c
   end.

Definition ClassMetamodel_getEReference (c : ClassMetamodel_ELink) : ClassMetamodel_EReference :=
   match c with
  | (ClassMetamodel_BuildELink c _) => c
   end.

Definition ClassMetamodel_instanceOfEClass (cmc: ClassMetamodel_EClass) (c : ClassMetamodel_EObject): bool :=
  if ClassMetamodel_eqEClass_dec (ClassMetamodel_getEClass c) cmc then true else false.

Definition ClassMetamodel_instanceOfEReference (cmr: ClassMetamodel_EReference) (c : ClassMetamodel_ELink): bool :=
  if ClassMetamodel_eqEReference_dec (ClassMetamodel_getEReference c) cmr then true else false.

Definition ClassMetamodel_getEObjectFromEAttributeValues (t : ClassMetamodel_EClass) : (ClassMetamodel_getEAttributeTypesByEClass t) -> ClassMetamodel_EObject :=
  match t with
  | ClassEClass => (fun (p: nat * string) => (ClassMetamodel_BuildEObject ClassEClass (BuildClass (fst p) (snd p))))
  | AttributeEClass => (fun (p: nat * bool * string) => (ClassMetamodel_BuildEObject AttributeEClass (BuildAttribute (fst (fst p)) (snd (fst p)) (snd p))))
  end.

Definition ClassMetamodel_getELinkFromERoleValues (t : ClassMetamodel_EReference) : (ClassMetamodel_getERoleTypesByEReference t) -> ClassMetamodel_ELink :=
  match t with
  | ClassAttributesEReference => (fun (p: Class * list Attribute) => (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes (fst p) (snd p))))
  | AttributeTypeEReference => (fun (p: Attribute * Class) => (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType (fst p) (snd p))))
  end.

Definition ClassMetamodel_toEClass (t : ClassMetamodel_EClass) (c : ClassMetamodel_EObject) : option (ClassMetamodel_getTypeByEClass t).
Proof.
  destruct c.
  destruct (ClassMetamodel_eqEClass_dec c t).
  - rewrite e in c0.
    exact (Some c0).
  - exact None.
Defined.



(*  
match c with
| ClassMetamodel_BuildEObject c0 d =>
    let s := ClassMetamodel_eqEClass_dec c0 t in
    match s with
    | left e => match e with
                     eq_refl => Some d
               end
    | right _ => None
    end
  end.
  
*)

Definition ClassMetamodel_toEReference (t : ClassMetamodel_EReference) (c : ClassMetamodel_ELink) : option (ClassMetamodel_getTypeByEReference t).
Proof.
  destruct c.
  destruct (ClassMetamodel_eqEReference_dec t c).
  - rewrite <- e in c0.
    exact (Some c0).
  - exact None.
Defined.

(* Generic functions *)

Definition ClassMetamodel_toEObjectFromClass (c :Class) : ClassMetamodel_EObject :=
  (ClassMetamodel_BuildEObject ClassEClass c).
Coercion ClassMetamodel_toEObjectFromClass : Class >-> ClassMetamodel_EObject.
Definition ClassMetamodel_toEObject (c : ClassMetamodel_EObject) : ClassMetamodel_EObject := c.

Definition ClassMetamodel_toEObjectFromAttribute (a :Attribute) : ClassMetamodel_EObject :=
  (ClassMetamodel_BuildEObject AttributeEClass a).
Coercion ClassMetamodel_toEObjectFromAttribute : Attribute >-> ClassMetamodel_EObject.
Definition ClassMetamodel_toELink (c : ClassMetamodel_ELink) : ClassMetamodel_ELink := c.

Definition ClassMetamodel_toEObjectOfEClass (t: ClassMetamodel_EClass) (e: ClassMetamodel_getTypeByEClass t) : ClassMetamodel_EObject :=
  (ClassMetamodel_BuildEObject t e).

Definition ClassMetamodel_toELinkOfEReference (t: ClassMetamodel_EReference) (e: ClassMetamodel_getTypeByEReference t) : ClassMetamodel_ELink :=
  (ClassMetamodel_BuildELink t e).

Definition ClassMetamodel_getId (c : ClassMetamodel_EObject) : nat :=
  match c with
  | (ClassMetamodel_BuildEObject ClassEClass c) => getClassId c
  | (ClassMetamodel_BuildEObject AttributeEClass a) => getAttributeId a
  end.

(*Definition allClasses (m : ClassModel) : list Class :=
  match m with BuildClassModel l _ => optionList2List (map (ClassMetamodel_toEClass ClassEClass) l) end.*)

(*Theorem allClassesInModel :
  forall (c : Class) (cm: ClassModel), (In c (allClasses cm)) -> (In (ClassMetamodel_BuildEObject ClassEClass c) (allClassModelElements cm)).
Proof.
  intros.
  destruct cm.
  unfold allClassModelElements.
  unfold allClasses in H.
  apply all_optionList2List_in_list in H.
  induction l.
  - inversion H.
  - simpl in H. simpl.
    destruct H.
    + unfold ClassMetamodel_toEClass in H.
      left.
      destruct (ClassMetamodel_eqEClass_dec (ClassMetamodel_getEClass a) ClassEClass).
      * destruct a.
        -- inversion H. reflexivity.
        -- inversion H.
      * inversion H.
    + right.
      apply IHl.
      apply H.
Qed.*)
  
(*Definition allAttributes (m : ClassModel) : list Attribute :=
  match m with BuildClassModel l _ => optionList2List (map (ClassMetamodel_toEClass AttributeEClass) l) end.*)

Fixpoint ClassMetamodel_getClassAttributesOnLinks (c : Class) (l : list ClassMetamodel_ELink) : option (list Attribute) :=
  match l with
  | (ClassMetamodel_BuildELink ClassAttributesEReference (BuildClassAttributes cl a)) :: l1 => if beq_Class cl c then Some a else ClassMetamodel_getClassAttributesOnLinks c l1
  | _ :: l1 => ClassMetamodel_getClassAttributesOnLinks c l1
  | nil => None
  end.

Definition getClassAttributes (c : Class) (m : Model ClassMetamodel_EObject ClassMetamodel_ELink) : option (list Attribute) :=
  ClassMetamodel_getClassAttributesOnLinks c (allModelLinks m).

Fixpoint ClassMetamodel_getAttributeTypeOnLinks (a : Attribute) (l : list ClassMetamodel_ELink) : option Class :=
  match l with
  | (ClassMetamodel_BuildELink AttributeTypeEReference (BuildAttributeType att c)) :: l1 => if beq_Attribute att a then Some c else ClassMetamodel_getAttributeTypeOnLinks a l1
  | _ :: l1 => ClassMetamodel_getAttributeTypeOnLinks a l1
  | nil => None
  end.

Definition getAttributeType (a : Attribute) (m : Model ClassMetamodel_EObject ClassMetamodel_ELink) : option Class :=
  match m with
    (BuildModel cs ls) => ClassMetamodel_getAttributeTypeOnLinks a ls
  end.

Definition ClassMetamodel_defaultInstanceOfEClass (c: ClassMetamodel_EClass) : (ClassMetamodel_getTypeByEClass c) :=
  match c with
  | ClassEClass => (BuildClass 0 "")
  | AttributeEClass => (BuildAttribute 0 false "")
  end.

(* Typeclass Instance *)

Instance ClassMetamodel : Metamodel ClassMetamodel_EObject ClassMetamodel_ELink ClassMetamodel_EClass ClassMetamodel_EReference :=
  {
    denoteModelClass := ClassMetamodel_getTypeByEClass;
    denoteModelReference := ClassMetamodel_getTypeByEReference;
    toModelClass := ClassMetamodel_toEClass;
    toModelReference := ClassMetamodel_toEReference;
    toModelElement := ClassMetamodel_toEObjectOfEClass;
    toModelLink := ClassMetamodel_toELinkOfEReference;
    bottomModelClass := ClassMetamodel_defaultInstanceOfEClass;

    (* Theorems *)
    eqModelClass_dec := ClassMetamodel_eqEClass_dec;
    eqModelReference_dec := ClassMetamodel_eqEReference_dec;

    (* Constructors *)
    BuildModelElement := ClassMetamodel_BuildEObject;
    BuildModelLink := ClassMetamodel_BuildELink;
  }.

Definition ClassModel := Model ClassMetamodel_EObject ClassMetamodel_ELink.
