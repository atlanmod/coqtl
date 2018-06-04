Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.

Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Definition Class2RelationalConcrete :=
  transformation Class2Relational from ClassMetamodel to RelationalMetamodel
    with m as ClassModel := [

       rule Class2Table
         from
           element c class ClassEClass from ClassMetamodel
             when true
         to
          [
           output "tab"
             element t class TableClass from RelationalMetamodel :=
               BuildTable (getClassId c) (getClassName c)
             links
               [
                 reference TableColumnsReference from RelationalMetamodel :=
                   attrs <- getClassAttributes c m;
                   cols <- resolveAll Class2Relational m "col" ColumnClass
                      (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                   return BuildTableColumns t cols
               ]
          ];

      rule Attribute2Column
        from
          element a class AttributeEClass from ClassMetamodel 
            when (negb (getAttributeDerived a))
        to
         [
          output "col"
            element c class ColumnClass from RelationalMetamodel := 
               BuildColumn (getAttributeId a) (getAttributeName a)
            links
              [
                reference ColumnReferenceReference from RelationalMetamodel :=
                  cl <- getAttributeType a m;
                  tb <- resolve Class2Relational m "tab" TableClass [ClassMetamodel_toEObject cl];
                  return BuildColumnReference c tb
              ] 
         ]

  ].

(* Unset Printing Notations.*)
(* Print Class2Relational. *)
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition Class2Relational := parseTransformation Class2RelationalConcrete.


Theorem All_classes_match :
  forall (cm : ClassModel) (c: Class) ,
    exists (r: RuleA ClassMetamodel_EClass RelationalMetamodel_EClass RelationalMetamodel_EReference),
      matchPattern Class2Relational cm [ClassMetamodel_toEObject c] = Some r.    
Proof.
  intros.
  exists (hd (BuildRuleA nil (BuildGuardExpressionA 0) nil) (TransformationA_getRules Class2Relational)).
  unfold matchPattern.
  reflexivity.
Qed.

Theorem All_classes_instantiate :
  forall (cm : ClassModel) (c: Class),
    exists (t: Table),
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c] = Some [RelationalMetamodel_toEObject t].
Proof.
  intros.
  exists (BuildTable (getClassId c) (getClassName c)).
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  reflexivity.
Qed.

Theorem Concrete_attributes_instantiate :
  forall (cm : ClassModel) (a: Attribute),
    exists (c: Column), getAttributeDerived a=false -> 
      instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a] = Some [RelationalMetamodel_toEObject c].
Proof.
  intros.
  exists (BuildColumn (getAttributeId a) (getAttributeName a)).
  intros.
  unfold instantiatePattern.
  unfold instantiateRuleOnPattern.
  simpl.
  rewrite H.
  reflexivity.
Qed.


