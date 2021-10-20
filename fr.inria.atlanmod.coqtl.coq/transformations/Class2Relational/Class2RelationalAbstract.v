Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.Syntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.

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

Instance C2RConfiguration : TransformationConfiguration := 
   Build_TransformationConfiguration ClassM RelationalM.
 
Instance Class2RelationalConfiguration : ModelingTransformationConfiguration C2RConfiguration :=
   Build_ModelingTransformationConfiguration C2RConfiguration ClassMetamodel RelationalMetamodel.

Definition Class2Relational :=
  buildTransformation 1
    [
      buildRule "Class2Table"
        (makeGuard [ClassClass] (fun m c => true))
        (makeIterator [ClassClass] (fun m c => 1))
        [buildOutputPatternElement "tab"
          (makeElement [ClassClass] TableClass
            (fun i m c => BuildTable (getClassId c) (getClassName c)))
            (makeLink [ClassClass] TableClass TableColumnsReference
            (fun tls i m c t =>
              attrs <- getClassAttributes c m;
              cols <- resolveAll tls m "col" ColumnClass 
                (singletons (map (ClassMetamodel_toObject AttributeClass) attrs));
              return BuildTableColumns t cols))
        ];
      buildRule "Attribute2Column"
        (makeGuard [AttributeClass] (fun m a => negb (getAttributeDerived a)))
        (makeIterator [AttributeClass] (fun m a => 1))
        [buildOutputPatternElement "col"
          (makeElement [AttributeClass] ColumnClass
            (fun i m a => BuildColumn (getAttributeId a) (getAttributeName a)))
            (makeLink [AttributeClass] ColumnClass ColumnReferenceReference
              (fun tls i m a c =>
                cl <- getAttributeType a m;
                tb <- resolve tls m "tab" TableClass [ClassMetamodel_toObject ClassClass cl];
                return BuildColumnReference c tb))
        ]
    ].
