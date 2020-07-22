(**
 CoqTL user theorem: Table_name_uniqueness
 Def: if all classes in the source model have unique name,
      then the target tables generated in the target model
      have unique name.
 **)

Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.Utils.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Table_name_uniqueness :
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class) (c2: Class), 
    In (ClassMetamodel_toObject c1) (allModelElements cm) -> 
    In (ClassMetamodel_toObject c2) (allModelElements cm) -> 
    c1 <> c2 -> 
    getClassName c1 <> getClassName c2) ->
(* postcondition *)  
(forall (t1: Table) (t2: Table), 
    In (RelationalMetamodel_toObject t1) (allModelElements rm) -> 
    In (RelationalMetamodel_toObject t2) (allModelElements rm) -> 
    t1 <> t2 -> 
    getTableName t1 <> getTableName t2).
Proof.
    intros.
    rewrite H in H1.
    rewrite H in H2.
    rewrite tr_execute_in_elements in H1.
    rewrite tr_execute_in_elements in H2.
    do 2 destruct H1, H2.
    destruct x, x0.
    - (* [] [] *) contradiction H4.
    - (* [] [x::_] *) contradiction H4.
    - (* [x::_] [] *) contradiction H5.
    - (* [x::_] [y::_] *) destruct x, x0.
        + (* [x] [y] *) do 2 destruct c, c0.
            * (*[c] [c]*) specialize (H0 c1 c2).
            apply allTuples_incl in H1.
            apply allTuples_incl in H2.
            unfold incl in H1.
            unfold incl in H2.
            specialize (H1 c1).
            specialize (H2 c2).
Admitted.
