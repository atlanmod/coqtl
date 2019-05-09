Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.



Theorem Table_name_uniqueness :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  apply tr_execute_surj_elements with (te:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [inst].
  destruct H as [Hinsm]. destruct H as [Hintp]. rename H into Hincltp.
  apply tr_instantiatePattern_surj_elements with (te:=t1) (tm:=rm) in inst.
  - { 
      destruct inst as [r]. destruct H as [Hrintr]. destruct H as [Hmatch]. rename H into Hinst.
      destruct sp eqn:sp_ca.
      -- assert ((matchPattern Class2Relational cm nil) = nil).
                {apply tr_matchPattern_sp_nil. }
         rewrite H in Hmatch.
         contradiction.
      -- destruct l eqn:l_ca.
         --- apply tr_instantiateRuleOnPattern_surj_elements with (te:=t1) (tm:=rm) (tr:=Class2Relational) in Hinst.  
              ----  destruct Hinst as [HrinMatch].
                    destruct H as [Hguard].
                    destruct H as [out].
                    destruct H as [it].
                    destruct H as [Hit].
                    destruct H as [Hout].
                    rename H into Heval.
                    destruct c eqn: c_ca;
                    destruct c0 eqn: c0_ca.
                    ----- (* ClassEClass *)
                          unfold Class2Relational in Hrintr.
                          destruct Hrintr as [r1|rrest].
                          ------ admit.
                          ------ destruct rrest as [r2|ctrdct].
                                 ------- rewrite <- r2 in Hguard.
                                         unfold  evalGuard in Hguard.
                                         simpl in Hguard.
                                         (* its ok to inversion here, or chose a better tactic*)
                                         inversion Hguard. 
                                 ------- contradiction.
                    ----- (* AttributeEClass *)
                          unfold Class2Relational in Hrintr.
                          destruct Hrintr as [r1|rrest].
                          ------ rewrite <- r1 in Hguard.
                                 unfold  evalGuard in Hguard.
                                 simpl in Hguard.
                                 (* its ok to inversion here, or chose a better tactic*)
                                 inversion Hguard. 
                          ------ destruct rrest as [r2|ctrdct].
                                 ------- admit.
                                 ------- contradiction.
              ---- assumption.
              ---- assumption.
              ---- assumption.
         --- inversion Hmatch.
    }
  - assumption.
  - assumption.
  - assumption.
Admitted.
