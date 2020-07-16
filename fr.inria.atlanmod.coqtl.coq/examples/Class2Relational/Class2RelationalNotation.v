Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.

Require Import core.ConcreteSyntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

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

Open Scope coqtl.

Definition Class2Relational :=
  transformation from ClassMetamodel to RelationalMetamodel by
    [
      rule "Class2Table"
      from [ClassEClass] where (fun m c => return true)
      for (fun m c => return 1)
      to [ 
         "tab": [ClassEClass] => TableClass :=
                (fun i m c => return BuildTable (getClassId c) (getClassName c)) 
                with [
                    : [ClassEClass] => TableClass => TableColumnsReference :=
                    (fun tls i m c t =>
                    attrs <- getClassAttributes c m;
                    cols <- resolveAll tls m "col" ColumnClass 
                      (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                    return BuildTableColumns t cols)
                ]
      ];

      rule "Attribute2Column"
      from [AttributeEClass] where (fun m a => return negb (getAttributeDerived a))
      for (fun m a => return 1)
      to [
         "col": [AttributeEClass] => ColumnClass :=
                (fun i m a => return (BuildColumn (getAttributeId a) (getAttributeName a))) 
                with [
                    : [AttributeEClass] => ColumnClass => ColumnReferenceReference :=
                    (fun tls i m a c =>
                    cl <- getAttributeType a m;
                    tb <- resolve tls m "tab" TableClass [ClassMetamodel_toEObject cl];
                    return BuildColumnReference c tb)
                ]
      ]
    ].

Close Scope coqtl.
