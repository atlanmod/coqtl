Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.Model.
Require Import core.CoqTL.

Require Import examples.ClassGraph2Tree.ClassMetamodel.
Require Import examples.ClassGraph2Tree.ClassMetamodelPattern.

Definition rootClass (m : ClassModel) : Class :=
  hd (ClassMetamodel_defaultInstanceOfEClass ClassEClass)
     (ClassMetamodel_allInstances ClassEClass m).

Definition nextPaths (p: list Class) (m: ClassModel) : list (list Class) :=
  match p with
  | c :: p' =>
    match getClassAttributes c m with
    | Some attrs =>
      map
        (fun a =>
           match getAttributeType a m with
           | Some cls => cls :: p
           | None => nil
           end
        )
        attrs
    | None => nil
    end
  | nil => nil
  end.

Fixpoint allPathsFix (m: ClassModel) (l : nat) (p: list Class) :  list (list Class) :=
  match l with
  | S l' => p :: concat (map (allPathsFix m l') (nextPaths p m))
  | 0 => [ p ]
  end.

Definition allPaths (m : ClassModel) (l : nat) : list (list Class) :=
  allPathsFix m l [ rootClass m ].

Definition ClassGraph2Tree' :=
  transformation ClassGraph2Tree from ClassMetamodel to ClassMetamodel
    with m as ClassModel := [

      rule Class2Class
        from
          element c class ClassEClass
        to [
          output "cl"
            element c' class ClassEClass :=
              BuildClass newId (getClassName c)
            links [
              reference ClassAttributesEReference :=
                attrs <- getClassAttributes c m;
                attrs' <- resolveAll ClassGraph2Tree m "at" AttributeEClass
                  (map (fun a:Attribute => [[ a ]]) attrs);
                return BuildClassAttributes c' attrs'
             ]
        ]
  ].

Definition ClassGraph2Tree := parseTransformation ClassGraph2Tree'.
