Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.

Require Import core.utils.tTop.
Require Import core.utils.CpdtTactics.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.



Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  apply tr_execute_surj_elements with (t1:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [inst].
  destruct H as [Hinsm]. destruct H as [Hintp]. rename H into Hincltp.
  apply tr_instantiatePattern_surj_elements with (t1:=t1) (tm:=rm) in inst.
  - { 
      destruct inst as [r]. destruct H as [Hrintr]. destruct H as [Hmatch]. rename H into Hinst.
      destruct sp eqn:sp_ca.
      -- inversion Hmatch.
      -- destruct l eqn:l_ca.
         --- apply tr_instantiateRuleOnPattern_surj_elements with (t1:=t1) (tm:=rm) in Hinst.  
              ----  destruct Hinst as [Hgpre].
                    destruct H as [Hguard].
                    destruct H as [outexpr].
                    destruct H as [HoutinOuts].
                    rename H into Heval.
                    unfold evalOutputPatternElementExpression in Heval.

(* The problem here is that:
     the signature of evalOutputPatternElementExpression does not have Rule as input,
     instead it computes a rule based on the given outexpression.
     so there are at least two Rules in the context, but Coq have no idea they are the same.
 *)
                    simpl in Heval.
                    admit.
              ---- assumption.
              ---- assumption.
              ---- assumption.
         --- inversion Hmatch.
    }
  - assumption.
  - assumption.
  - assumption.
Admitted.
