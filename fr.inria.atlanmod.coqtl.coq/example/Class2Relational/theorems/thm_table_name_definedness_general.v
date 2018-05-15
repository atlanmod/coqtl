Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.Utils_Top.
Require Import core.CoqTL.

Require Import example.Class2Relational.
Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.

Theorem Table_name_definedness_by_surj_without_proofengineering :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
    ((forall (c1 : Class), In (ClassMetamodel_toEObject c1) (allModelElements cm) -> (negb (beq_string (getClassName c1) ""))) /\       (* precondition 1*)
     (forall (a1 : Attribute), In (ClassMetamodel_toEObject a1) (allModelElements cm) -> (negb (beq_string (getAttributeName a1) "")))) (* precondition 2 *) ->
    ((forall (t1 : Table), In (RelationalMetamodel_toEObject t1) (allModelElements rm) -> (negb (beq_string (getTableName t1) ""))) /\      (* postcondition 1 *)
      (forall (co1 : Column), In (RelationalMetamodel_toEObject co1) (allModelElements rm) -> (negb (beq_string (getColumnName co1) "")))). (* postcondition 2 *)
Proof.
  intros cm rm H Hpre.
  split.
  (* post1 *)
  - intros.
    apply tr_surj with (t1:=t1) in H.
    Focus 2. assumption.
    Focus 1.
    destruct H as [sp]. destruct H as [tp]. destruct H as [r].
    destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec]. destruct H as [Hinclsp]. destruct H as [incltp].
    rename H into Hmatch.
    simpl in Hmatch.
    destruct Hpre as [Hpre1 Hpre2].
    destruct sp eqn:sp_ca.
    - inversion Hmatch.
    - destruct l eqn:l_ca.
      Focus 2.
      + inversion Hmatch.
      Focus 1.
      + destruct c eqn:c_ca. 
        * destruct c0 eqn:c0_ca.
          ** simpl in Hmatch.
             inversion Hmatch.
             rewrite <- H1 in Hexec.
             unfold instantiateRuleOnPattern in Hexec. simpl in Hexec.
             rewrite <- Hexec in Hintp.
             simpl in Hintp.
             destruct Hintp.
             unfold RelationalMetamodel_toEObject in H.
             unfold RelationalMetamodel_toEObjectFromTable in H.
             apply rel_invert in H.
             rewrite <- H.
             simpl.
             unfold incl in Hinclsp.
             assert (In c ([ClassMetamodel_BuildEObject ClassEClass c1])). {
               simpl. left. symmetry. assumption.
             }
             
             apply Hinclsp in H2.
             rewrite c_ca in H2.
             simpl in H2. 
             apply Hpre1 in H2.
             assumption.
             contradiction H.
          ** simpl in Hmatch.
             destruct (getAttributeDerived c1) eqn:derived_ca.
             simpl in Hmatch.
             inversion Hmatch.
             simpl in Hmatch.
             inversion Hmatch.
             rewrite <- H1 in Hexec.
             unfold instantiateRuleOnPattern in Hexec. 
             unfold executeRuleOnPattern in Hexec. 
             simpl in Hexec. 
             rewrite derived_ca in Hexec. 
             simpl in Hexec.
             rewrite <- Hexec in Hintp.
             simpl in Hintp.
             destruct Hintp eqn: Hintp_ca.
              - done.
             - done. 
  (* post2 *)
  - intros.
    apply tr_surj with (t1:=co1) in H.
    Focus 2. assumption.
    Focus 1.
    destruct H as [sp]. destruct H as [tp]. destruct H as [r].
    destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec]. destruct H as [Hinclsp]. destruct H as [incltp].
    rename H into Hmatch.
    simpl in Hmatch.
    destruct Hpre as [Hpre1 Hpre2].
    destruct sp eqn:sp_ca.
    - inversion Hmatch.
    - destruct l eqn:l_ca.
      Focus 2.
      + inversion Hmatch.
      Focus 1.
      + destruct c eqn:c_ca. 
        * destruct c0 eqn:c0_ca.
          ** simpl in Hmatch.
             inversion Hmatch.
             rewrite <- H1 in Hexec.
             unfold instantiateRuleOnPattern in Hexec. simpl in Hexec.
             rewrite <- Hexec in Hintp.
             simpl in Hintp.
             destruct Hintp.
             - done.
             - done.
          ** simpl in Hmatch.
             destruct (getAttributeDerived c1) eqn:derived_ca.
             simpl in Hmatch.
             inversion Hmatch.
             simpl in Hmatch.
             inversion Hmatch.
             rewrite <- H1 in Hexec.
             unfold instantiateRuleOnPattern in Hexec. 
             unfold executeRuleOnPattern in Hexec. 
             simpl in Hexec. 
             rewrite derived_ca in Hexec. 
             simpl in Hexec.
             rewrite <- Hexec in Hintp.
             simpl in Hintp.
             destruct Hintp.
             - unfold RelationalMetamodel_toEObject in H.
               unfold RelationalMetamodel_toEObjectFromTable in H.
               apply rel_invert in H.
               rewrite <- H.
               simpl.
               unfold incl in Hinclsp.
               assert (In c ([ClassMetamodel_BuildEObject AttributeEClass c1])). {
                 simpl. left. symmetry. assumption.
               }
               
               apply Hinclsp in H2.
               rewrite c_ca in H2.
               simpl in H2. 
               apply Hpre2 in H2.
               assumption.
               contradiction H.
Qed.



