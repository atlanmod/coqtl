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
    In (ClassMetamodel_toObjectOfClass ClassClass c1) (allModelElements cm) -> 
    In (ClassMetamodel_toObjectOfClass ClassClass c2) (allModelElements cm) -> 
    c1 <> c2 -> 
    getClassName c1 <> getClassName c2) ->
(* postcondition *)  
(forall (t1: Table) (t2: Table), 
    In (RelationalMetamodel_toObjectOfClass TableClass t1) (allModelElements rm) -> 
    In (RelationalMetamodel_toObjectOfClass TableClass t2) (allModelElements rm) -> 
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
                specialize (H1 (ClassMetamodel_toObjectOfClass ClassClass c1)).
                specialize (H2 (ClassMetamodel_toObjectOfClass ClassClass c2)).
                assert (In (ClassMetamodel_toObjectOfClass ClassClass c1) [ClassMetamodel_toObjectOfClass ClassClass c1]). 
                { left. reflexivity. }
                assert (In (ClassMetamodel_toObjectOfClass ClassClass c2) [ClassMetamodel_toObjectOfClass ClassClass c2]). 
                { left. reflexivity. }
                specialize (H0 (H1 H6)).
                specialize (H0 (H2 H7)).
                simpl in H4, H5.
                destruct H4, H5. 
                -- inversion H4.
Admitted.
