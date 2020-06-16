Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Metamodel.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

(* module Class2Relational; 
   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes.resolve('col')
         )
    }
    rule Attribute2Column {
        from 
          a : Attribute (not a.derived)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- a.type.resolve('tab')
          )
    }
   } *)

Definition Class2Relational :=
  (@BuildTransformation ClassMetamodel_EObject ClassMetamodel_ELink RelationalMetamodel_EObject RelationalMetamodel_ELink
    [(BuildRule "Class2Table" 
      (fun (m:ClassModel) (c:list ClassMetamodel_EObject) => 
        return true)
      (fun (m:ClassModel) (c:list ClassMetamodel_EObject) => nil)
      [(BuildOutputPatternElement "tab"
        (fun _ (m: ClassModel) (c:list ClassMetamodel_EObject) => 
          None)
        [(BuildOutputPatternElementReference
          (fun (tr: MatchedTransformation) _ (m: ClassModel) (c:list ClassMetamodel_EObject) (t: RelationalMetamodel_EObject) =>
                    None))])]);
      (BuildRule "Attribute2Column" 
        (fun (m:ClassModel) (c:list ClassMetamodel_EObject) => 
          return true)
        (fun (m:ClassModel) (c:list ClassMetamodel_EObject) => nil)
        [(BuildOutputPatternElement "col"
          (fun _ (m: ClassModel) (c:list ClassMetamodel_EObject) => 
            None)
          [(BuildOutputPatternElementReference
            (fun (tr: MatchedTransformation) _ (m: ClassModel) (c:list ClassMetamodel_EObject) (t: RelationalMetamodel_EObject) =>
                      None))])])]).

(*Definition Class2Relational :=
  (BuildTransformation
     ClassMetamodel RelationalMetamodel
     [(BuildRule
         ClassMetamodel RelationalMetamodel
         "Class2Table"
         [ClassEClass] (fun (m: ClassModel) (c:Class) => true)
         unit (fun (m: ClassModel) (c:Class) => [tt])
         [(BuildOutputPatternElement
             ClassMetamodel RelationalMetamodel 
             [ClassEClass] "tab" TableClass
             (fun _ (m: ClassModel) (c:Class) => BuildTable (getClassId c) (getClassName c))
             [(BuildOutputPatternElementReference
                 ClassMetamodel RelationalMetamodel
                 [ClassEClass] TableClass TableColumnsReference
                 (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                    _ (m: ClassModel) (c:Class) (t: Table) =>
                    attrs <- getClassAttributes c m;
                    cols <- resolveAll tr m "col" ColumnClass
                            (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                    return BuildTableColumns t cols))])]);
        (BuildRule
           ClassMetamodel RelationalMetamodel
           "Attribute2Column"
           [AttributeEClass] (fun (m: ClassModel) (a: Attribute) => negb (getAttributeDerived a))
           unit (fun (m: ClassModel) (a: Attribute) => [tt])
           [(BuildOutputPatternElement
               ClassMetamodel RelationalMetamodel
               [AttributeEClass] "col" ColumnClass
               (fun _ (m: ClassModel) (a: Attribute) => BuildColumn (getAttributeId a) (getAttributeName a))
               [(BuildOutputPatternElementReference
                   ClassMetamodel RelationalMetamodel
                   [AttributeEClass] ColumnClass ColumnReferenceReference
                   (fun (tr: MatchedTransformation ClassMetamodel RelationalMetamodel)
                      _ (m: ClassModel) (a: Attribute) (c: Column) =>
                      cl <- getAttributeType a m;
                            tb <- resolve tr m "tab" TableClass [ClassMetamodel_toEObject cl];
                            return BuildColumnReference c tb))])])]).*)
