Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.
Require Import core.CoqTL.
Require Import core.Metamodel.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.



Definition Class2Relational :=
  (BuildTransformation
     ClassMetamodel RelationalMetamodel
     [(BuildRule
         ClassMetamodel RelationalMetamodel
         [ClassEClass]
         (fun (m: ClassModel) (c:Class) => true)
         [(BuildOutputPatternElement
             ClassMetamodel RelationalMetamodel
             "tab"
             [ClassEClass] TableClass 
             (fun (m: ClassModel) (c:Class) => BuildTable (getClassId c) (getClassName c))
             [(BuildOutputPatternElementReference
                 ClassMetamodel RelationalMetamodel
                 [ClassEClass] TableClass TableColumnsReference
                 (fun (t: MatchedTransformation ClassMetamodel RelationalMetamodel)
                    (m: ClassModel) (c:Class) (t: Table) =>
                    attrs <- getClassAttributes c m;
                      cols <- Some nil;
                      return BuildTableColumns t cols))])]);
        (BuildRule
           ClassMetamodel RelationalMetamodel
           [AttributeEClass]
           (fun (m: ClassModel) (a: Attribute) => true)
           [(BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               "col"
               [AttributeEClass] ColumnClass 
               (fun (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
               [(BuildOutputPatternElementReference
                   ClassMetamodel RelationalMetamodel
                   [AttributeEClass] ColumnClass ColumnReferenceReference
                   (fun (t: MatchedTransformation ClassMetamodel RelationalMetamodel)
                      (m: ClassModel) (a: Attribute) (c: Column) =>
                      None))])])]).

(* Definition Class2Relational :=
  (BuildTransformation ClassMetamodel RelationalMetamodel
  [
     (BuildRule [ClassEClass]
        (fun (m: ClassModel) (c: Class) => true)
        [
        (BuildOutputPatternElement "tab" TableClass
            (fun (m: ClassModel) (c: Class) => BuildTable (getClassId c) (getClassName c))
            [
                (BuildOutputPatternElementReference TableColumnReference
                    (fun (m: ClassModel) (c: Class) (t: Table) (Class2Relational: Transformation) =>
                        reference TableColumnsReference from RelationalMetamodel :=
                        attrs <- getClassAttributes c m;
                        cols <- resolveAll Class2Relational m "col" ColumnClass
                            (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                        return BuildTableColumns t cols))
            ])                               
        ]);
     (BuildRule [AttributeEClass]
        (fun (m: ClassModel) (a: Attribute) => true)
        [
        (BuildOutputPatternElement "col" ColumnClass
            (fun (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
            [
                (BuildOutputPatternElementReference ColumnReferenceReference
                    (fun (m: ClassModel) (a: Attribute) (c: Column) (Class2Relational: Transformation) =>
                        reference ColumnReferenceReference from RelationalMetamodel :=
                            cl <- getAttributeType a m;
                            tb <- resolve Class2Relational m "tab" TableClass [ClassMetamodel_toEObject cl];
                            return BuildColumnReference c tb))
            ])
        ])
  ]). *)

Unset Printing Notations.

(* Print Class2Relational. *)
(* Check Class2Relational. *)
