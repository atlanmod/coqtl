Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import String.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

(*Require Import core.Semantics.
Require Import core.Certification.*)
Require Import core.Semantics_v2.
Require Import core.Certification_v2.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.

Theorem Relational_id_definedness :
forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)   (forall (c1 : ClassMetamodel_EObject) (c2: ClassMetamodel_EObject), In c1 (allModelElements cm) -> In c2 (allModelElements cm) -> c1 <> c2 -> ClassMetamodel_getId c1 <> ClassMetamodel_getId c2) ->
  (* postcondition *)  (forall (t1 : RelationalMetamodel_EObject) (t2 : RelationalMetamodel_EObject), In t1 (allModelElements rm)-> In t2 (allModelElements rm) -> t1 <> t2 -> RelationalMetamodel_getId t1 <> RelationalMetamodel_getId t2).
Proof.
  (** Clean context *)
  intros cm rm H Hpre t1 t2 Hintm Hintm2 ineq.  
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
  apply tr_instantiateRuleOnPattern_in with (tr0:=Class2Relational) in H6.
  destruct H6. destruct H6.
  rename x into i.
  rename x1 into tp1.

  (** Unfolding theorem tr_instantiateIterationOnPattern_in *)
  assert  (exists tp : list  RelationalMetamodel_EObject,
          instantiateIterationOnPattern r cm sp i = return tp /\ In t1 tp).
  { exists tp1. crush. }
  apply tr_instantiateIterationOnPattern_in in H7.
  destruct H7. destruct H7.
  unfold instantiateElementOnPattern in H8.
  unfold matchRuleOnPattern' in H5.
  rewrite H5 in H8.

  (** Clean context *)
  rewrite tr in Hintm2.
  apply tr_execute_in_elements in Hintm2.
  destruct Hintm2. destruct H9. destruct H9. destruct H10.

   (** Unfolding theorem tr_instantiatePattern_in *)
  assert (exists tp : list RelationalMetamodel_EObject,
             instantiatePattern Class2Relational cm x1 = return tp /\ In t2 tp).
  { exists x2. split. crush. crush. }
  apply tr_instantiatePattern_in in H12.
  destruct H12. destruct H12. destruct H12.
  rename x3 into r2. rename x4 into tp2. rename x1 into sp2.

  (** Unfolding theorem tr_matchPattern_in *)
  apply tr_matchPattern_in in H12.
  destruct H12.

  (** Unfolding theorem tr_instantiateRuleOnPattern_in *)
  assert (exists tp : list  RelationalMetamodel_EObject,
          instantiateRuleOnPattern r2 cm sp2 = return tp /\ In t2 tp).
  { exists tp2. crush. }
  apply tr_instantiateRuleOnPattern_in with (tr0:=Class2Relational) in H15.
  destruct H15. destruct H15.
  rename x1 into i2.
  clear H13. clear tp2.
  rename x3 into tp2.

  (** Unfolding theorem tr_instantiateIterationOnPattern_in *)
  assert  (exists tp : list  RelationalMetamodel_EObject,
          instantiateIterationOnPattern r2 cm sp2 i2 = return tp /\ In t2 tp).
  { exists tp2. crush. }
  apply tr_instantiateIterationOnPattern_in in H13.
  destruct H13. destruct H13.
  unfold instantiateElementOnPattern in H16.
  unfold matchRuleOnPattern' in H14.
  rewrite H14 in H16.

  unfold Class2Relational in H3.
  simpl in H3.

  unfold Class2Relational in H12.
  simpl in H12.
  
  (* rewrite t1 *)
  destruct H3.
  + destruct (nth_error (evalIterator r cm sp) i).
    ++   generalize dependent x.
         generalize dependent r0.        
         rewrite <- H3.
         simpl.
         intros.
         destruct H7.
         +++ rewrite <- H7 in H8.
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction ClassMetamodel cm [ClassEClass] Table
                       (fun (_ : ClassModel) (c : Class) => BuildTable (getClassId c) (getClassName c)) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ destruct c eqn: c_ca.
                        destruct c0 eqn: c0_ca.
                        ++++++ simpl in eval_fun.
                           destruct l.
                           +++++++  inversion eval_fun.
                               inversion H8.
                               rewrite <- H18.
                               simpl.
                               (* rewrite t2 *)
                                destruct H12.
                                * destruct (nth_error (evalIterator r2 cm sp2) i2).
                                  **   generalize dependent x1.
                                       generalize dependent r1.        
                                       rewrite <- H12.
                                       simpl.
                                       intros.
                                       destruct H13.
                                       *** rewrite <- H13 in H16.
                                           unfold evalOutputPatternElement in H16. simpl in H16.
                                           destruct (Expressions.evalFunction ClassMetamodel cm [ClassEClass] Table
                                                     (fun (_ : ClassModel) (c : Class) => BuildTable (getClassId c) (getClassName c)) sp2) eqn: eval_fun2.
                                           **** unfold Expressions.evalFunction in eval_fun2.
                                                unfold Expressions.evalFunctionFix in eval_fun2.
                                                destruct sp2 eqn: sp_ca2.
                                                ***** inversion eval_fun2.
                                                ***** destruct c2 eqn: c2_ca.
                                                      destruct c3 eqn: c3_ca.
                                                      ****** simpl in eval_fun2.
                                                         destruct l.
                                                         *******  inversion eval_fun2.
                                                                  inversion H16.
                                                                  rewrite <- H20.
                                                                  simpl.
                                                                  (* case1: t1 is table, t2 is table *)
                                                                  assert (c <> c2). {  
                                                                    rewrite <- H21 in ineq.
                                                                    rewrite <- H19 in ineq.
                                                                    rewrite c_ca.
                                                                    rewrite c2_ca.
                                                                    assert (t <> t0). crush.
                                                                    rewrite <- H20 in H17.
                                                                    rewrite <- H18 in H17.
                                                                    injection.
                                                                    intros.
                                                                    apply Class_invert in H22.
                                                                    rewrite H22 in H17.
                                                                    crush.
                                                                  }
                                                                  assert (In c (allModelElements cm)). { crush. }
                                                                  assert (In c2 (allModelElements cm)). { crush. }
                                                                  specialize (Hpre c c2 H22 H23 H17). 
                                                                  unfold ClassMetamodel_getId in Hpre.
                                                                  rewrite c_ca in Hpre. rewrite c2_ca in Hpre. auto.
                                                         ******* crush.
                                                      ****** simpl in eval_fun2. inversion eval_fun2.
                                           **** inversion H16.
                                       *** crush.
                                  ** crush.
                                * destruct H12.
                                  destruct (nth_error (evalIterator r2 cm sp2) i2).
                                  **   generalize dependent x1.
                                       generalize dependent r1.        
                                       rewrite <- H12.
                                       simpl.
                                       intros.
                                       destruct H13.
                                       *** (* case2: t1 is table, t2 is column *) 
                                           rewrite <- H13 in H16.
                                           unfold evalOutputPatternElement in H16. simpl in H16.
                                           destruct (Expressions.evalFunction ClassMetamodel cm 
                                                      [AttributeEClass] Column
                                                      (fun (_ : ClassModel) (a : Attribute) =>
                                                       BuildColumn (getAttributeId a) (getAttributeName a)) sp2) eqn: eval_fun2.
                                           **** unfold Expressions.evalFunction in eval_fun2.
                                                unfold Expressions.evalFunctionFix in eval_fun2.
                                                destruct sp2 eqn: sp_ca2.
                                                ***** inversion eval_fun2.
                                                ***** destruct c3 eqn: c3_ca.
                                                      destruct c4 eqn: c4_ca.
                                                      ****** simpl in eval_fun2. inversion eval_fun2.
                                                      ****** simpl in eval_fun2. destruct l.
                                                         *******  inversion eval_fun2.
                                                                  inversion H16.
                                                                  rewrite <- H20.
                                                                  simpl.
                                                                  assert (c <> c3). {  crush. }
                                                                  assert (In c (allModelElements cm)). { crush. }
                                                                  assert (In c3 (allModelElements cm)). { crush. }
                                                                  specialize (Hpre c c3 H22 H23 H17). 
                                                                  unfold ClassMetamodel_getId in Hpre.
                                                                  rewrite c_ca in Hpre. rewrite c3_ca in Hpre. auto.
                                                         ******* crush.
                                           **** inversion H16.
                                       *** inversion H13.
                                  ** inversion H16.
                                  ** inversion H12.
                           +++++++ inversion eval_fun.
                        ++++++ simpl in eval_fun. inversion eval_fun.
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
             unfold evalOutputPatternElement in H8. simpl in H8.
             destruct (Expressions.evalFunction ClassMetamodel cm
                       [AttributeEClass] Column
                       (fun (_ : ClassModel) (a : Attribute) =>
                        BuildColumn (getAttributeId a) (getAttributeName a)) sp) eqn: eval_fun.
             ++++ unfold Expressions.evalFunction in eval_fun.
                  unfold Expressions.evalFunctionFix in eval_fun.
                  destruct sp eqn: sp_ca.
                  +++++ inversion eval_fun.
                  +++++ destruct c0 eqn: c0_ca.
                        destruct c1 eqn: c1_ca.
                        ++++++ simpl in eval_fun. inversion eval_fun.
                        ++++++ simpl in eval_fun. destruct l.
                           +++++++  inversion eval_fun.
                               inversion H8.
                               rewrite <- H18.
                               simpl.
                               (* rewrite t2 *)
                                destruct H12.
                                * destruct (nth_error (evalIterator r2 cm sp2) i2).
                                  **   generalize dependent x1.
                                       generalize dependent r1.        
                                       rewrite <- H12.
                                       simpl.
                                       intros.
                                       destruct H13.
                                       *** rewrite <- H13 in H16.
                                           unfold evalOutputPatternElement in H16. simpl in H16.
                                           destruct (Expressions.evalFunction ClassMetamodel cm [ClassEClass] Table
                                                     (fun (_ : ClassModel) (c : Class) => BuildTable (getClassId c) (getClassName c)) sp2) eqn: eval_fun2.
                                           **** unfold Expressions.evalFunction in eval_fun2.
                                                unfold Expressions.evalFunctionFix in eval_fun2.
                                                destruct sp2 eqn: sp_ca2.
                                                ***** inversion eval_fun2.
                                                ***** destruct c3 eqn: c3_ca.
                                                      destruct c4 eqn: c4_ca.
                                                      ****** simpl in eval_fun2.
                                                         destruct l.
                                                         *******  inversion eval_fun2.
                                                                  inversion H16.
                                                                  rewrite <- H20.
                                                                  simpl.
                                                                  (* case3: t1 is column, t2 is table *)
                                                                  assert (c0 <> c3). {  
                                                                    crush.
                                                                  }
                                                                  assert (In c0 (allModelElements cm)). { crush. }
                                                                  assert (In c3 (allModelElements cm)). { crush. }
                                                                  specialize (Hpre c0 c3 H22 H23 H17). 
                                                                  unfold ClassMetamodel_getId in Hpre.
                                                                  rewrite c0_ca in Hpre. rewrite c3_ca in Hpre. auto.
                                                         ******* crush.
                                                      ****** simpl in eval_fun2. inversion eval_fun2.
                                           **** inversion H16.
                                       *** crush.
                                  ** crush.
                                * destruct H12.
                                  destruct (nth_error (evalIterator r2 cm sp2) i2).
                                  **   generalize dependent x1.
                                       generalize dependent r1.        
                                       rewrite <- H12.
                                       simpl.
                                       intros.
                                       destruct H13.
                                       *** (* case2: t1 is column, t2 is column *) 
                                           rewrite <- H13 in H16.
                                           unfold evalOutputPatternElement in H16. simpl in H16.
                                           destruct (Expressions.evalFunction ClassMetamodel cm 
                                                      [AttributeEClass] Column
                                                      (fun (_ : ClassModel) (a : Attribute) =>
                                                       BuildColumn (getAttributeId a) (getAttributeName a)) sp2) eqn: eval_fun2.
                                           **** unfold Expressions.evalFunction in eval_fun2.
                                                unfold Expressions.evalFunctionFix in eval_fun2.
                                                destruct sp2 eqn: sp_ca2.
                                                ***** inversion eval_fun2.
                                                ***** destruct c4 eqn: c4_ca.
                                                      destruct c5 eqn: c5_ca.
                                                      ****** simpl in eval_fun2. inversion eval_fun2.
                                                      ****** simpl in eval_fun2. destruct l.
                                                         *******  inversion eval_fun2.
                                                                  inversion H16.
                                                                  rewrite <- H20.
                                                                  simpl.
                                                                  assert (c0 <> c4). { 
                                                                    rewrite <- H21 in ineq.
                                                                    rewrite <- H19 in ineq.
                                                                    rewrite c0_ca.
                                                                    rewrite c4_ca.
                                                                    assert (c <> c3). crush.
                                                                    rewrite <- H20 in H17.
                                                                    rewrite <- H18 in H17.
                                                                    injection.
                                                                    intros.
                                                                    apply Class_invert in H22.
                                                                    rewrite H22 in H17.
                                                                    crush.
                                                                  }
                                                                  assert (In c0 (allModelElements cm)). { crush. }
                                                                  assert (In c4 (allModelElements cm)). { crush. }
                                                                  specialize (Hpre c0 c4 H22 H23 H17). 
                                                                  unfold ClassMetamodel_getId in Hpre.
                                                                  rewrite c0_ca in Hpre. rewrite c4_ca in Hpre. auto.
                                                         ******* crush.
                                           **** inversion H16.
                                       *** inversion H13.
                                  ** inversion H16.
                                  ** inversion H12.
                           +++++++ inversion eval_fun.

             ++++ inversion H8.
         +++ inversion H7.
    ++ inversion H8.
    ++ inversion H3.
Qed.


