Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.

Require Import HSM.
Require Import FSM.

Definition HSM2FSMConcrete :=
  transformation HSM2FSM from HSMetamodel to FSMMetamodel
    with m as HSMModel := [

       rule Class2Table
         from
           element c class ClassEClass from ClassMetamodel
             when true
         to
          [
           output "tab"
             element t class TableClass from RelationalMetamodel :=
               BuildTable (getClassId c) (getClassName c)
             links
               [
                 reference TableColumnsReference from RelationalMetamodel :=
                   attrs <- getClassAttributes c m;
                   cols <- resolveAll Class2Relational m "col" ColumnClass
                      (singletons (map (A:=Attribute) ClassMetamodel_toEObject attrs));
                   return BuildTableColumns t cols
               ]
          ];


  ].

(* Unset Printing Notations.*)
(* Print Class2Relational. *)
(* Compute maxArity (parseTransformation Class2Relational). *)

Definition HSM2FSM := parseTransformation HSM2FSMConcrete.



