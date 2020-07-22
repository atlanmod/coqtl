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

Theorem Table_name_uniqueness:
forall (cm : ClassModel) (rm : RelationalModel), 
(* transformation *) 
    rm = execute Class2Relational cm ->
(* precondition *)   
(forall (c1: Class) (c2: Class), 
    In (ClassMetamodel_toObject ClassClass c1) (allModelElements cm) -> 
    In (ClassMetamodel_toObject ClassClass c2) (allModelElements cm) -> 
    c1 <> c2 -> 
    getClassName c1 <> getClassName c2) ->
(* postcondition *)  
(forall (t1: Table) (t2: Table), 
    In (RelationalMetamodel_toObject TableClass t1) (allModelElements rm) -> 
    In (RelationalMetamodel_toObject TableClass t2) (allModelElements rm) -> 
    t1 <> t2 -> 
    getTableName t1 <> getTableName t2).
Proof.
    intros.
    rewrite H in H1, H2.
    rewrite tr_execute_in_elements in H1, H2.
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
                unfold incl in H1, H2.
                specialize (H1 (ClassMetamodel_toObject ClassClass c1)).
                specialize (H2 (ClassMetamodel_toObject ClassClass c2)).
                assert (In (ClassMetamodel_toObject ClassClass c1) [ClassMetamodel_toObject ClassClass c1]). 
                { left. reflexivity. }
                assert (In (ClassMetamodel_toObject ClassClass c2) [ClassMetamodel_toObject ClassClass c2]). 
                { left. reflexivity. }
                specialize (H0 (H1 H6)).
                specialize (H0 (H2 H7)).
                simpl in H4, H5.
                destruct H4, H5. 
                -- apply rel_invert in H4.
                   apply rel_invert in H5.
                   rewrite <- H4.
                   rewrite <- H5.
                   apply H0.
                   rewrite <- H4 in H3.
                   rewrite <- H5 in H3.
                   destruct c1, c2.
                   simpl in H3.
                   unfold not.
                   intros.
                   unfold not in H3.
                   inversion H8.
                   rewrite H10 in H3.
                   rewrite H11 in H3.
                   contradiction.
                -- contradiction. 
                -- contradiction.
                -- contradiction.
            * (*[c] [a]*) destruct c2. destruct b.
                -- contradiction.
                -- simpl in H5. destruct H5. inversion H5. contradiction. 
            * (*[a] [c]*) destruct c1. destruct b.
                -- contradiction.
                -- simpl in H4. destruct H4. inversion H4. contradiction.
            * (*[a] [a]*) destruct c1. destruct b.
                -- contradiction.
                -- simpl in H4. destruct H4. inversion H4. contradiction.
        + (* [x] [y;y';_] *)
            do 2 destruct c0, c1.
            * contradiction.
            * contradiction.
            * contradiction.
            * contradiction.
        + (* [x;x';_] [y] *)
            do 2 destruct c, c1.
            * contradiction.
            * contradiction.
            * contradiction.
            * contradiction.
        + (* [x;x';_] [y;y';_] *)
            do 2 destruct c, c1.
            * contradiction.
            * contradiction.
            * contradiction.
            * contradiction.
Qed.
