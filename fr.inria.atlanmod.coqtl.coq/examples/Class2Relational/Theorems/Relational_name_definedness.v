Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.

Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

(* Require Import core.CoqTL. *)
Require Import core.CoqTL_v2.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Relational_name_definedness :
forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_EObject), In c1 (allModelElements cm) -> (ClassMetamodel_getName c1 <> ""%string)) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_EObject), In t1 (allModelElements rm) -> (RelationalMetamodel_getName t1 <> ""%string)). 
Proof.
  (** Clean context *)
  intros cm rm H Hpre t1 Hintm.  
  remember H as tr.
  clear Heqtr.
  rewrite tr in Hintm.
  apply tr_execute_in_elements in Hintm.
  destruct Hintm. destruct H0. destruct H0. destruct H1.

  (** Unfolding theorem tr_instantiatePattern_in *)
  assert (exists tp : list RelationalMetamodel_EObject,
             instantiatePattern Class2Relational cm x = return tp /\ In t1 tp).
  { exists x0. split. crush. crush. }
  apply tr_instantiatePattern_in in H3.
  destruct H3. destruct H3. destruct H3.
  rename x1 into r. rename x2 into tp. rename x into sp.

  (** Unfolding theorem tr_matchPattern_in *)
  apply tr_matchPattern_in in H3.
  destruct H3.

  (** Unfolding theorem tr_instantiateRuleOnPattern_in *)
  assert (exists tp : list  RelationalMetamodel_EObject,
          instantiateRuleOnPattern r cm sp = return tp /\ In t1 tp).
  { exists tp. crush. }
  apply tr_instantiateRuleOnPattern_in with (tr:=Class2Relational) in H6.
  destruct H6. destruct H6.
  rename x into i.
  rename x1 into tp1.

  (** Unfolding theorem tr_instantiateIterationOnPattern_in *)
  assert  (exists tp : list  RelationalMetamodel_EObject,
          instantiateIterationOnPattern r cm sp i = return tp /\ In t1 tp).
  { exists tp1. crush. }
  apply tr_instantiateIterationOnPattern_in in H7.
  destruct H7. destruct H7.
  (* suggests missing theorem about instantiateElementonpattern and evalOutputpatternelement
     but perhaps this is intended, since at some point, we will have a function interfaces
     to functions defined in Expression.v
   *)
  unfold instantiateElementOnPattern in H8.
  (* suggests missing theorem about adaptor function matchRuleOnpattern' and matchruleonpattern
     although, in my opinion, we should avoid adaptor function in general.
   *)
  unfold matchRuleOnPattern' in H5.
  rewrite H5 in H8.
  unfold Class2Relational in H3.
  simpl in H3.
  destruct H3.
  + destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.        
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             (* suggests missing theorem about evalOutputPatternElement and evalFunction *)
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction ClassMetamodel cm [ClassEClass] Table
                       (fun (_ : ClassModel) (c : Class) => BuildTable (getClassId c) (getClassName c)) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ destruct c eqn: c_ca.
                        destruct c0 eqn: c0_ca.
                         * simpl in eval_fun.
                           destruct l.
                           **  inversion eval_fun.
                               inversion H8.
                               rewrite <- H10.
                               simpl.
                               specialize (Hpre c).
                               unfold incl in H0.
                               specialize (H0 c). simpl in H0.
                               assert (In c (allModelElements cm)). { crush. }
                               specialize (Hpre H9).
                               unfold ClassMetamodel_getName in Hpre.
                               rewrite c_ca in Hpre. auto.
                           **  inversion eval_fun.
                         * simpl in eval_fun. inversion eval_fun.
             ++++ inversion H8.
         +++ crush.
    ++ crush.
  + destruct H3.
    destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.        
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             (* suggests missing theorem about evalOutputPatternElement and evalFunction *)
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction ClassMetamodel cm [AttributeEClass] Column
         (fun (_ : ClassModel) (a : Attribute) =>
          BuildColumn (getAttributeId a) (getAttributeName a)) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ 
                    destruct c0 eqn: c0_ca.
                    destruct c1 eqn: c1_ca.
                         * simpl in eval_fun. inversion eval_fun.
                         * simpl in eval_fun.
                           destruct l.
                           **  inversion eval_fun.
                               inversion H8.
                               rewrite <- H10.
                               simpl.
                               specialize (Hpre c0).
                               unfold incl in H0.
                               specialize (H0 c0). simpl in H0.
                               assert (In c0 (allModelElements cm)). { crush. }
                               specialize (Hpre H9).
                               unfold ClassMetamodel_getName in Hpre.
                               rewrite c0_ca in Hpre. auto.      
                           ** inversion eval_fun.
             ++++ inversion H8.
         +++ inversion H7.
    ++ inversion H8.
    ++ inversion H3.
Qed.  
