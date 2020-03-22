Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.
Require Import core.CoqTL.
Require Import core.Metamodel.

Require Import examples.Class2RelationalMV.ClassMetamodel.
Require Import examples.Class2RelationalMV.RelationalMetamodel.


Definition Class2Relational :=
  (BuildTransformation
     ClassMetamodel RelationalMetamodel
     [(BuildRule
         ClassMetamodel RelationalMetamodel
         "Class2Table"
         [ClassEClass] (fun (m: ClassModel) (c:Class) => true)
         unit (fun (m: ClassModel) (c:Class) => [tt])
         [(BuildOutputPatternElement
             ClassMetamodel RelationalMetamodel 
             [ClassEClass] "tab" TableEClass
             (fun _ (m: ClassModel) (c:Class) => BuildTable (getClassId c) (getClassName c))
             [(BuildOutputPatternElementReference
                 ClassMetamodel RelationalMetamodel
                 [ClassEClass] TableEClass TableColumnsEReference
                 (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                    _ (m: ClassModel) (c:Class) (t: Table) =>
                    attrs <- getClassAttributes c m;
                    cols <- resolveAll tr m "col" ColumnEClass
                            (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                    key <- resolve tr m "key" ColumnEClass [ClassMetamodel_toEObject c];
                    return BuildTableColumns t (key::cols)))]);
           (BuildOutputPatternElement
             ClassMetamodel RelationalMetamodel 
             [ClassEClass] "key" ColumnEClass
             (fun _ (m: ClassModel) (c:Class) => BuildColumn (getClassId c) (getClassName c ++ "id")) (* which id unique might not hold *)
             nil)  
         ]);
        (BuildRule
           ClassMetamodel RelationalMetamodel
           "SinglevaluedAttribute2Column"
           [AttributeEClass] (fun (m: ClassModel) (a: Attribute) => negb (getAttributeMultiValued a))
           unit (fun (m: ClassModel) (a: Attribute) => [tt])
           [(BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "col" ColumnEClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
               [(BuildOutputPatternElementReference
                   ClassMetamodel RelationalMetamodel
                   [AttributeEClass] ColumnEClass ColumnReferenceEReference
                   (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                      _ (m: ClassModel) (a: Attribute) (c: Column) =>
                            cl <- getAttributeType a m;
                            tb <- resolve tr m "tab" TableEClass [ClassMetamodel_toEObject cl];
                            return BuildColumnReference c tb))])]);
        (BuildRule
           ClassMetamodel RelationalMetamodel
           "MultivaluedAttribute2Column"
           [AttributeEClass] (fun (m: ClassModel) (a: Attribute) => (getAttributeMultiValued a))
           unit (fun (m: ClassModel) (a: Attribute) => [tt])
           [(BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "col" ColumnEClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
               [(BuildOutputPatternElementReference
                   ClassMetamodel RelationalMetamodel
                   [AttributeEClass] ColumnEClass ColumnReferenceEReference
                   (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                      _ (m: ClassModel) (a: Attribute) (c: Column) =>
                            tb <- resolve tr m "pivot" TableEClass [ClassMetamodel_toEObject a];
                            return BuildColumnReference c tb))]);
            (BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "pivot" TableEClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildTable (getAttributeId a) (getAttributeName a ++ "Pivot"))
               [(BuildOutputPatternElementReference
                 ClassMetamodel RelationalMetamodel
                 [AttributeEClass] TableEClass TableColumnsEReference
                 (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                    _ (m: ClassModel) (a: Attribute) (t: Table) =>
                            psrc <- resolve tr m "psrc" ColumnEClass [ClassMetamodel_toEObject a];
                            ptrg <- resolve tr m "ptrg" ColumnEClass [ClassMetamodel_toEObject a];
                            return BuildTableColumns t [psrc; ptrg]))]);
            (BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "psrc" ColumnEClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) "key")
               nil);
            (BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "ptrg" ColumnEClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
               [(BuildOutputPatternElementReference
                   ClassMetamodel RelationalMetamodel
                   [AttributeEClass] ColumnEClass ColumnReferenceEReference
                   (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                      _ (m: ClassModel) (a: Attribute) (c: Column) =>
                            cl <- getAttributeType a m;
                            tb <- resolve tr m "tab" TableEClass [ClassMetamodel_toEObject cl];
                            return BuildColumnReference c tb))])])]).


