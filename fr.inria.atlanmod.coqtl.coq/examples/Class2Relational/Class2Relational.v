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
  buildTransformation
    [
      buildRule "Class2Table"
        (makeGuard [ClassEClass] (fun m c => return true))
        (makeIterator [ClassEClass] (fun m c => [0]))
        [buildOutputPatternElement "tab"
          (makeElement [ClassEClass] TableClass
            (fun i m c => return BuildTable (getClassId c) (getClassName c)))
          [buildOutputPatternElementReference
            (makeLink [ClassEClass] TableClass TableColumnsReference
              (fun tls i m c t =>
                 attrs <- getClassAttributes c m;
                 cols <- resolveAll tls m "col" ColumnClass (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                 return BuildTableColumns t cols))
          ]
        ];
      buildRule "Attribute2Column"
        (makeGuard [AttributeEClass] (fun m a => return negb (getAttributeDerived a)))
        (makeIterator [AttributeEClass] (fun m a => [0]))
        [buildOutputPatternElement "col"
          (makeElement [AttributeEClass] ColumnClass
            (fun i m a => return (BuildColumn (getAttributeId a) (getAttributeName a))))
          [buildOutputPatternElementReference
            (makeLink [AttributeEClass] ColumnClass ColumnReferenceReference
              (fun tls i m a c =>
                cl <- getAttributeType a m;
                tb <- resolve tls m "tab" TableClass [ClassMetamodel_toEObject cl];
                return BuildColumnReference c tb))
          ]
        ]
    ].
