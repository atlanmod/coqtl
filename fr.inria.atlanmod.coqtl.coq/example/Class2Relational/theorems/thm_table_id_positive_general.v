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


Lemma app_inj_tail2 :
    forall (A: Type) (a b: A), [a] = [b] -> a = b.
Proof.
intros.
inversion H.
reflexivity.
Qed.
    


Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (@allModelElements _ _ cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (@allModelElements _ _ rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
Proof.
  intros cm rm H Hpre t1 Hintm.  
  apply tr_surj with (t1:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [r].
  destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec]. destruct H as [Hinclsp]. destruct H as [incltp].
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
        ** (* t is the only element in tp *)
           assert (exists (t: Table), instantiatePattern Class2Relational cm [ClassMetamodel_toEObject c1] = Some [RelationalMetamodel_toEObject t]).
           { apply All_classes_instantiate. }
           destruct H.
           rewrite Hexec in H.
           inversion H.
           rewrite H1 in Hintp.
           simpl in Hintp.
           (* t = BuildTable (getClassId c1) (getClassName c1) *)
           destruct Hintp.
           *** unfold instantiatePattern in Hexec.           
               unfold instantiateRuleOnPattern in Hexec. 
               simpl in Hexec.
               inversion Hexec.    
               rewrite H1 in H3.
               (* BUG? inversion H3 doesn't give the following assertion *)
               assert (RelationalMetamodel_toEObject x = (RelationalMetamodel_BuildEObject TableClass (BuildTable (getClassId c1) (getClassName c1)))).
               { apply app_inj_tail2 in H3. auto. }
               unfold RelationalMetamodel_toEObject in H2.
               rewrite <- H0.
               rewrite H2.
               simpl.
               assert (In c ([ClassMetamodel_BuildEObject ClassEClass c1])). { simpl. left. symmetry. assumption. }
               apply Hinclsp in H4. apply Hpre in H4. 
               unfold ClassMetamodel_getId in H4.
               rewrite  c_ca in H4.
               assumption.
           *** contradiction.
        ** (* t is the only element in tp *)
           rename c0 into a0.
           rename c1 into a1.
           assert (exists (col: Column), getAttributeDerived a1=false -> 
                     instantiatePattern Class2Relational cm [ClassMetamodel_toEObject a1] = Some [RelationalMetamodel_toEObject col]).
           { apply Concrete_attributes_instantiate. }
           destruct H.
           rewrite Hexec in H.
           unfold instantiatePattern in Hexec.           
           unfold instantiateRuleOnPattern in Hexec. 
           simpl in Hexec.
           destruct (getAttributeDerived a1) eqn:derived_ca.
           *** inversion Hexec.
           *** assert (false = false). { reflexivity. }
               apply H in H0.
               inversion H0.
               rewrite H2 in Hintp.
               simpl in Hintp.
               (* col = BuildColumn ... *)
               destruct Hintp.
               *** 
                   inversion Hexec.    
                   rewrite H2 in H4.
                   assert (RelationalMetamodel_toEObject x = RelationalMetamodel_toEObjectOfEClass ColumnClass (BuildColumn (getAttributeId a1) (getAttributeName a1))).
                   { apply app_inj_tail2 in H4. auto. }
                   unfold RelationalMetamodel_toEObject in H2.
                   rewrite <- H1.
                   rewrite H3.
                   simpl.
                   assert (In c ([ClassMetamodel_BuildEObject AttributeEClass a1])). { simpl. left. symmetry. assumption. }
                   apply Hinclsp in H5. apply Hpre in H5. 
                   unfold ClassMetamodel_getId in H5.
                   rewrite  c_ca in H5.
                   assumption.
               *** contradiction.
Qed.
