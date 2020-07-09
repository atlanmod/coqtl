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
  @BuildTransformation ClassMetamodel_EObject ClassMetamodel_ELink RelationalMetamodel_EObject RelationalMetamodel_ELink
    [
      BuildRule "Class2Table"
        (makeGuard [ClassEClass] (fun (m:ClassModel) c => return true))
        (makeIterator [ClassEClass] (fun (m:ClassModel) c => [0]))
        [BuildOutputPatternElement "tab"
          (makeElement [ClassEClass] TableClass
            (fun _ (m: ClassModel) c => return BuildTable (getClassId c) (getClassName c)))
          [BuildOutputPatternElementReference
            (makeLink [ClassEClass] TableClass TableColumnsReference
              (fun (tr: list TraceLink) _ (m: ClassModel) c t =>
                 attrs <- getClassAttributes c m;
                 cols <- resolveAll tr m "col" ColumnClass (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                 return BuildTableColumns t cols))
          ]
        ];
      BuildRule "Attribute2Column"
        (makeGuard [AttributeEClass] (fun (m:ClassModel) a => return negb (getAttributeDerived a)))
        (makeIterator [AttributeEClass] (fun (m:ClassModel) a => [0]))
        [BuildOutputPatternElement "col"
          (makeElement [AttributeEClass] ColumnClass
            (fun _ (m: ClassModel) a => return (BuildColumn (getAttributeId a) (getAttributeName a))))
          [BuildOutputPatternElementReference
            (makeLink [AttributeEClass] ColumnClass ColumnReferenceReference
              (fun (tr: list TraceLink) _ (m: ClassModel) a c =>
                cl <- getAttributeType a m;
                tb <- resolve tr m "tab" TableClass [ClassMetamodel_toEObject cl];
                return BuildColumnReference c tb))
          ]
        ]
    ].
