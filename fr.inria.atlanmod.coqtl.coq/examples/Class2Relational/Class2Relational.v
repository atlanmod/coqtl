Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.Utils.

Require Import core.ConcreteSyntax.
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

Open Scope coqtl.

Definition Class2Relational' :=
  transformation ClassMetamodel RelationalMetamodel
  [
    rule "Class2Table"
    from [ClassClass]
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
