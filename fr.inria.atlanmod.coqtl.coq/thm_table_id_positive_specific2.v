Require Import Class2Relational.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.
Require Import CoqTL.
Require Import Utils.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import Coq.Logic.Eqdep_dec.

Lemma matchPattern_in_getRules :
    forall (sm: ClassModel) (r: Rule ClassMetamodel RelationalMetamodel) (sp: list ClassMetamodel_EObject),
      (matchPattern (matchPhase Class2Relational sm) sp) = Some r -> In r (getRules Class2Relational sm).
  Proof.
    unfold getRules.
    intros tr sm.
    induction (matchPhase Class2Relational tr).
    - intros. inversion H.
    - intros.
      simpl.
      simpl in H.
      destruct (matchRuleOnPattern a sp) in H.
      -- left. inversion H. reflexivity.
      -- right. apply IHl in H. apply H.
  Qed.
  
  
Theorem tr_surj_Class2Relational : 
  forall (sm : ClassModel) (tm: RelationalModel) (t1 : RelationalMetamodel_EObject),
    tm = execute Class2Relational sm -> In t1 (allModelElements tm) -> 
    (exists (sp : list ClassMetamodel_EObject) (tp : list RelationalMetamodel_EObject) (r : Rule ClassMetamodel RelationalMetamodel),
        In r (getRules Class2Relational sm) /\
        In t1 tp /\
        instantiateRuleOnPattern r sp = tp /\
        incl sp (allModelElements sm) /\
        incl tp (allModelElements tm)  /\
        matchPattern (getRules Class2Relational sm) sp = Some r).
  Proof.
    intros sm tm t1 H0.
    rewrite H0. simpl.
    intros.
    apply concat_map_exists in H. destruct H. destruct H.
    remember (matchPattern (matchPhase Class2Relational sm) x) as r'.
    destruct r'.
    
    Focus 2.
    unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction. 
    
    Focus 1.
    exists x, (instantiatePattern (matchPhase Class2Relational sm) x),r.
    
    split.
    - apply matchPattern_in_getRules with (sp:=x).
      rewrite Heqr'. reflexivity.
    - split.
      + assumption.
      + split.
        * unfold instantiatePattern.
          rewrite <- Heqr'. reflexivity.
        * split.
          ** unfold allTuples in H.
             apply tuples_up_to_n_incl with (n:=(maxArity (getRules Class2Relational sm))).
             assumption.
          ** split.
             *** apply concat_map_incl. assumption.
             *** unfold getRules. symmetry. assumption.
  Qed.
  
  
Theorem Table_id_positive_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
      (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> ClassMetamodel_getId c1 > 0) (* precondition *) ->
        (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> RelationalMetamodel_getId t1 > 0). (* postcondition *)
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
      * destruct c0 eqn:c0_ca.
        ** simpl in Hmatch.
           inversion Hmatch.
           rewrite <- H0 in Hexec.
           unfold instantiateRuleOnPattern in Hexec. simpl in Hexec.
           rewrite <- Hexec in Hintp.
           simpl in Hintp.
           destruct Hintp.
           rewrite <- H.
           simpl.
           unfold incl in Hinclsp.
           assert (In c ([ClassMetamodel_BuildEObject ClassEClass c1])). {
             simpl. left. symmetry. assumption.
           }
           apply Hinclsp in H1. apply Hpre in H1.
           unfold ClassMetamodel_getId in H1.
           rewrite  c_ca in H1.
           assumption.
           contradiction H.
        ** simpl in Hmatch.
           destruct (getAttributeDerived c1) eqn:derived_ca.
           simpl in Hmatch.
           inversion Hmatch.
           simpl in Hmatch.
           inversion Hmatch.
           rewrite <- H0 in Hexec.
           unfold instantiateRuleOnPattern in Hexec. unfold executeRuleOnPattern in Hexec. simpl in Hexec. rewrite derived_ca in Hexec. simpl in Hexec.
           rewrite <- Hexec in Hintp.
           simpl in Hintp.
           destruct Hintp.
           rewrite <- H.
           simpl.
           unfold incl in Hinclsp.
           assert (In c ([ClassMetamodel_BuildEObject AttributeEClass c1])). {
             simpl. left. symmetry. assumption.
           }
           apply Hinclsp in H1. apply Hpre in H1.
           unfold ClassMetamodel_getId in H1.
           rewrite  c_ca in H1.
           assumption.
           contradiction H.
Qed.