Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.

Require Import core.utils.Utils.

Require Import core.modeling.ConcreteSyntax.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ModelingMetamodel.
Require Import core.modeling.ConcreteExpressions.
Require Import core.modeling.Parser.

Require Import Class2Relational.ClassMetamodel.
Require Import Class2Relational.RelationalMetamodel.

Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
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

Open Scope coqtl.

Definition Class2Relational' :=
  transformation
  [
    rule "Class2Table"
    from [ClassClass]
    where (fun m a => true)
    to [elem [ClassClass] TableClass "tab"
        (fun i m c => BuildTable (getClassId c) (getClassName c))
        [link [ClassClass] TableClass TableColumnsReference
          (fun tls i m c t =>
            maybeBuildTableColumns t
              (maybeResolveAll tls m "col" ColumnClass 
                (maybeSingletons (getClassAttributesObjects c m))))]]
    ;
    rule "Attribute2Column"
    from [AttributeClass]
    where (fun m a => negb (getAttributeDerived a))
    to [elem [AttributeClass] ColumnClass "col"
        (fun i m a => BuildColumn (getAttributeId a) (getAttributeName a))
        [link [AttributeClass] ColumnClass ColumnReferenceReference
          (fun tls i m a c =>
            maybeBuildColumnReference c
              (maybeResolve tls m "tab" TableClass 
                (maybeSingleton (getAttributeTypeObject a m))))]]
  ].

Definition Class2Relational := parse Class2Relational'.

Close Scope coqtl.
