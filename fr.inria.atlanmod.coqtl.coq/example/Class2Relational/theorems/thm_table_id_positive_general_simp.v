Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import example.Class2Relational.
Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.



Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  apply tr_surj_elements with (t1:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [r].
  destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec']. destruct H as [Hinclsp]. destruct H as [incltp].
  assert (instantiatePattern Class2Relational cm sp = return tp).
  { apply tr_instantiate_pattern_derivable with (tm:=rm) (r:=r); assumption. }
  rename H0 into Hexec.
  rename H into Hmatch.
  simpl in Hmatch.
  destruct sp eqn:sp_ca.
  - inversion Hmatch.
  - destruct l eqn:l_ca.
    Focus 2.
    + inversion Hmatch.
    Focus 1.
    + destruct c eqn:c_ca. 
      destruct c0 eqn:c0_ca.
      ++ unfold instantiatePattern in Hexec.
         unfold instantiateRuleOnPattern in Hexec.
         simpl in Hexec.
         inversion Hexec as [Htp].
         rewrite <- Htp in Hintp.
         simpl in Hintp.
         destruct Hintp as [Hintp1|Hintp2].
          +++ rewrite <- Hintp1. simpl.
             assert (In c ([ClassMetamodel_BuildEObject ClassEClass c1])). { simpl. left. symmetry. assumption. }
             apply Hinclsp in H. apply Hpre in H. 
             unfold ClassMetamodel_getId in H.
             rewrite  c_ca in H.
             assumption.
          +++ contradiction.
      ++ unfold instantiatePattern in Hexec.           
         unfold instantiateRuleOnPattern in Hexec. 
         simpl in Hexec.
         destruct (getAttributeDerived c1) eqn:derived_ca.
         *** inversion Hexec.
         *** simpl in Hexec.
             inversion Hexec as [Htp].
             rewrite <- Htp in Hintp.
             simpl in Hintp.
             destruct Hintp as [Hintp1|Hintp2].
             +++ rewrite <- Hintp1. simpl.
                 assert (In c ([ClassMetamodel_BuildEObject AttributeEClass c1])). { simpl. left. symmetry. assumption. }
                 apply Hinclsp in H. apply Hpre in H. 
                 unfold ClassMetamodel_getId in H.
                 rewrite  c_ca in H.
                 assumption.
             +++ contradiction.
Qed.
