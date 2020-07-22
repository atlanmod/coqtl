Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.Semantics.
Require Import core.Metamodel.
Require Import core.Expressions.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

(* module Class2Relational; 
   create OUT : RelationalMetamodel from IN : ClassMetamodel;

   rule Class2Table {
       from 
         c : Class
       to 
         tab: Table (
           id <- c.id,
           name <- c.name,
           columns <- c.attributes->collect(a | thisModule.resolve(a, 'col'))
         )
    }
    rule Attribute2Column {
        from 
          a : Attribute (not a.derived)
        to 
          col: Column (
            id <- a.id,
            name <- a.name,
            reference <- thisModule.resolve(a.type, 'tab')
          )
    }
   } *)

Definition Class2Relational :=
  buildTransformation
    [
      buildRule "Class2Table" [ClassClass]
        (makeGuard [ClassClass] (fun m c => true))
        (makeIterator [ClassClass] (fun m c => 1))
        [buildOutputPatternElement "tab"
          (makeElement [ClassClass] TableClass
            (fun i m c => BuildTable (getClassId c) (getClassName c)))
          [buildOutputPatternElementReference
            (makeLink [ClassClass] TableClass TableColumnsReference
            (fun tls i m c t =>
              attrs <- getClassAttributes c m;
              cols <- resolveAll tls m "col" ColumnClass 
                (singletons (map (ClassMetamodel_toObject AttributeClass) attrs));
              return BuildTableColumns t cols))
          ]
        ];
      buildRule "Attribute2Column" [AttributeClass]
        (makeGuard [AttributeClass] (fun m a => negb (getAttributeDerived a)))
        (makeIterator [AttributeClass] (fun m a => 1))
        [buildOutputPatternElement "col"
          (makeElement [AttributeClass] ColumnClass
            (fun i m a => BuildColumn (getAttributeId a) (getAttributeName a)))
          [buildOutputPatternElementReference
            (makeLink [AttributeClass] ColumnClass ColumnReferenceReference
              (fun tls i m a c =>
                cl <- getAttributeType a m;
                tb <- resolve tls m "tab" TableClass [ClassMetamodel_toObject ClassClass cl];
                return BuildColumnReference c tb))
          ]
        ]
    ].
