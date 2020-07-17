(**

 CoqTL user theorem: Relational_name_definedness

 Def: if all objects in the source model have name defined,
      then the target objects generated in the target model
      have name defined.

 DO NOT COMPILE.

 old proof that rely on coqtl implementation, put here as a reference.
 
 **)
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

(* try cast x to type t, if succ and results x1, do e1, else do e2 *)
Notation "  x1 '<=' '[[' t ']]' x '|' 'SUCC' e1 'FAIL' e2 " :=
(match toModelClass t x with
| Some x1 => e1
| None => e2
end)
(right associativity, at level 70).

Theorem tr_surj_elements : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (t1 : TargetModelElement),
        In t1 (allModelElements tm) ->
        (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
            incl sp (allModelElements sm) /\
            In t1 tp /\
            incl tp (allModelElements tm) /\
            instantiatePattern tr sm sp = Some tp).
  Proof.
    intros tr sm tm H0 t1.
    rewrite H0. simpl.
    intros.
    apply concat_map_option_exists in H.
    destruct H. destruct H.
    rename x into sp1.
    remember (matchPattern tr sm sp1) as r'.
    destruct r'.
    
    2: {
      unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction.
    }
    1: {
      remember (instantiatePattern tr sm sp1) as tp_temp.
      destruct tp_temp eqn:tp1_case.
      2: {
        contradiction.
      }
      1: {
        rename l into tp1.
        exists sp1, tp1.
        repeat split.
        - apply tuples_up_to_n_incl with (n:=(maxArity tr)).
          assumption.
        - assumption.
        - apply concat_map_option_incl with (a:=sp1). assumption. symmetry. assumption.
        - symmetry. assumption.
      }
    }
  Qed.

Theorem Table_name_definedness_by_surj :
  forall (cm : ClassModel) (rm : RelationalModel), 
    rm = execute Class2Relational cm (* transformation *) ->
    ((forall (c1 : Class), In (ClassMetamodel_toEObject c1) (@allModelElements _ _ cm) -> (negb (beq_string (getClassName c1) ""))) /\       (* precondition 1*)
     (forall (a1 : Attribute), In (ClassMetamodel_toEObject a1) (@allModelElements _ _ cm) -> (negb (beq_string (getAttributeName a1) "")))) (* precondition 2 *) ->
    ( forall (t1 : RelationalMetamodel_EObject),
        In t1 (@allModelElements _ _ rm) ->
          (table1 <= [[TableEClass]] t1  | SUCC (negb (beq_string (getTableName table1) "")) FAIL true) /\    (* postcondition 1*)
          (column1 <= [[ColumnEClass]] t1 | SUCC (negb (beq_string (getColumnName column1) "")) FAIL true)).   (* postcondition 2*)
Proof.
  (* general bookkeeping *)
  intros cm rm H Hpre t1 Hintm.
  remember H as tr.
  clear Heqtr.
  apply tr_surj_elements with (t1:=t1) in H.
  Focus 2. assumption.
  Focus 1.
  destruct H as [sp]. destruct H as [tp]. destruct H as [Hinclsp]. destruct H as [Hintp]. destruct H as [incltp]. rename H into Hexec.
  destruct Hpre as [Hpre1 Hpre2].
  
  try destruct sp eqn:sp_ca; inversion Hexec. (* try ... inversion Hexec; elimin impossible case *)
  try destruct l eqn:l_ca; inversion Hexec.   (* try ... inversion Hexec; elimin impossible case *)
  (* post1 and post2 needs to be proved here*)
  destruct c eqn:c_ca.
  destruct clec_arg eqn:c0_ca.
  (* c0 = ClassEClass, prove post1 *)
  -  unfold instantiatePattern in Hexec.           
     unfold instantiateRuleOnPattern in Hexec. 
     simpl in Hexec.
     inversion Hexec as [Htp].
     rewrite <- Htp in Hintp.
     simpl in Hintp.
     destruct Hintp.
     + rewrite <- H.
       assert (In c ([Build_ClassMetamodel_EObject ClassEClass c0])). { simpl. left. symmetry. assumption. }
                                                                     apply Hinclsp in H2.
       rewrite c_ca in H2.
       apply Hpre1 in H2.
       split.
       simpl.
       * rewrite H2.
         done.
       * done.
     + done.
  (* c0 = AttributeEClass, prove post2 *)  
  - unfold instantiatePattern in Hexec.           
    unfold instantiateRuleOnPattern in Hexec. 
    unfold matchPattern in Hexec. 

    simpl in Hexec.
    destruct (getAttributeMultiValued c0) eqn:derived_ca; simpl in Hexec. 
    + inversion Hexec.
    + rewrite derived_ca in Hexec.
      simpl in Hexec.
      inversion Hexec as [Htp].
      rewrite <- Htp in Hintp.
      simpl in Hintp.
      destruct Hintp.
      * rewrite <- H.
        assert (In c ([Build_ClassMetamodel_EObject AttributeEClass c0])). { simpl. left. symmetry. assumption. }
                                                                          apply Hinclsp in H2.
        rewrite c_ca in H2.
        apply Hpre2 in H2.
        done.
      * done.
Qed.