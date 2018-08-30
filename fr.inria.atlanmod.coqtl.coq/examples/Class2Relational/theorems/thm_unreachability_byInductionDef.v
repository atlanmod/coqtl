Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import Omega.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.tTop.
Require Import core.utils.CpdtTactics.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.


Lemma rel_elink_invert : 
  forall (t: RelationalMetamodel_EReference) (t1 t2: RelationalMetamodel_getTypeByEReference t), Build_RelationalMetamodel_ELink t t1 = Build_RelationalMetamodel_ELink t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqEReference_dec.
Qed.


Lemma rel_invert : 
  forall (t: RelationalMetamodel_EClass) (t1 t2: RelationalMetamodel_getTypeByEClass t), Build_RelationalMetamodel_EObject t t1 = Build_RelationalMetamodel_EObject t t2 -> t1 = t2.
Proof.
intros.
inversion H.
apply inj_pair2_eq_dec in H1.
exact H1.
apply RelationalMetamodel_eqEClass_dec.
Qed.

Lemma lem_beq_Column_refl : 
 forall (c: Column),
   beq_Column c c = true.
Proof.
intros.
destruct c.
unfold beq_Column.
simpl.
assert (beq_string s0 s0 = true). {apply lem_beq_string_id. }
assert (beq_string s s = true). {apply lem_beq_string_id. }
rewrite H H0.
simpl.
auto.
Qed.

Lemma lem_beq_Table_refl:
 forall (a: Table),
   beq_Table a a = true.
Proof.
intros.
destruct a.
unfold beq_Table.
simpl.
assert (beq_string s0 s0 = true). { apply lem_beq_string_id. }
rewrite <- H.
assert (beq_string s s = true). { apply lem_beq_string_id. }
rewrite H0.
simpl.
auto.
Qed.

Lemma lem_beq_Table_id:
 forall (a1 a2: Table),
   beq_Table a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Table in H.
unfold "&&" in H.
destruct (beq_string (getTableId a1) (getTableId a2)) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (lem_beq_string_eq2) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1 H.
  auto.
- congruence.
Qed.

Lemma lem_beq_Column_id:
 forall (a1 a2: Column),
   beq_Column a1 a2 = true -> a1 = a2.
Proof.
intros.
unfold beq_Column in H.
unfold "&&" in H.
destruct (beq_string (getColumnId a1) (getColumnId a2)) eqn: ca1.
- apply (lem_beq_string_eq2) in H.
  apply (lem_beq_string_eq2) in ca1.
  destruct a1,a2.
  simpl in ca1, H.
  rewrite ca1 H.
  auto.
- congruence.
Qed.

Lemma eq_class_table:
  (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (t1 t2 : Table) (c1 c2: Class),
     In (RelationalMetamodel_toEObject t1) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c1::nil))) -> 
     In (RelationalMetamodel_toEObject t2) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c2::nil))) ->
     t1 = t2 ->
     c1 = c2).
Proof.
intros cm rm tr t1 t2 c1 c2  Hinc_t1_sp1 Hinc_t2_sp2 Heq_tables.
unfold instantiatePattern in Hinc_t1_sp1, Hinc_t2_sp2.
simpl in Hinc_t1_sp1, Hinc_t2_sp2.
try destruct Hinc_t1_sp1; destruct Hinc_t2_sp2; crush.
- rewrite <- H in H0.
  apply rel_invert in H0.
  inversion H0.
  destruct c1, c2.
  simpl in H2, H3.
  repeat apply lem_string_app_inv_tail in H2.
  rewrite H2 H3.
  done.
Qed.


Definition reachable_class_step (m: ClassModel) (x y: Class) : Prop :=
  In (ClassMetamodel_toEObject x) (allModelElements m) /\
  In (ClassMetamodel_toEObject y) (allModelElements m) /\ 
  match (getClassAttributes x m) with
   | Some l =>  exists (attr:Attribute), In (ClassMetamodel_toEObject attr) (allModelElements m) /\ 
                                   In attr l /\
                                   getAttributeType attr m = Some y
   | None => False
  end.




Inductive ReachableClass (m : ClassModel) (x: Class): Class -> Prop :=
| reachable_class_refl : ReachableClass m x x
| reachable_class_trans : forall (y z:Class), 
                          reachable_class_step m x y ->
                           ReachableClass m y z -> 
                           ReachableClass m x z.



Lemma ReachableClass_transitive :
 forall (m: ClassModel) (x y z:Class), 
  ReachableClass m x y ->
   ReachableClass m y z -> 
    ReachableClass m x z.
Proof.
intros.
induction H.
- done.
- pose (IHReachableClass H0) as H2.
  apply (@reachable_class_trans m x y z).
  - done.
  - done.
Qed.


Definition reachable_table_step (m: RelationalModel) (x y: Table) := 
  In (RelationalMetamodel_toEObject x) (allModelElements m) /\ 
  In (RelationalMetamodel_toEObject y) (allModelElements m) /\
  match (getTableColumns x m) with
   | Some l => exists (col: Column), In (RelationalMetamodel_toEObject col) (allModelElements m) /\ 
                                In col l /\ 
                                getColumnReference col m = Some y
   | None => False
  end.

Inductive ReachableTable (m : RelationalModel) (x: Table): Table -> Prop :=
| reachable_table_refl : ReachableTable m x x
| reachable_table_trans : forall (y z:Table), 
                           reachable_table_step m x y ->
                            ReachableTable m y z -> 
                              ReachableTable m x z. 

Lemma ReachableTable_transitive :
 forall (m: RelationalModel) (x y z:Table), 
  ReachableTable m x y ->
   ReachableTable m y z -> 
    ReachableTable m x z.
Proof.
intros.
induction H.
- done.
- pose (IHReachableTable H0) as Hind.
  apply (@reachable_table_trans m x y z).
  - done.
  - done.
Qed.



Lemma lem_inc_tp_rm:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute),
     In (ClassMetamodel_toEObject a) (allModelElements cm) ->
       incl (optionListToList (applyPattern Class2Relational cm (ClassMetamodel_toEObject a::nil))) (allModelLinks rm)).
Proof.
intros cm rm tr attr Hinc_attr_cm .
destruct (applyPattern Class2Relational cm (ClassMetamodel_toEObject attr::nil)) eqn: attr_guard_ca.
+ rewrite tr. simpl.
  apply concat_map_option_incl with (a:=(ClassMetamodel_toEObject attr::nil)).
  - assert (In (ClassMetamodel_toEObject attr::nil) (allTuples Class2Relational cm)).
    { unfold allTuples.
      simpl.
      unfold prod_cons.
      induction (allModelElements cm).
      - simpl. done.
      - simpl.
        simpl in Hinc_attr_cm.
        destruct Hinc_attr_cm.
        - left.
          rewrite H.
          done.
        - right.
          simpl.
          apply IHl0.
          done.
    }
  assumption.
  - assumption. 
+ done.
Qed.





Lemma lem_getColumnReference:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t : Table) (col: Column),
     getColumnReference col rm = return t ->
       In (Build_RelationalMetamodel_ELink ColumnReferenceEReference (BuildColumnReference col t)) (allModelLinks rm) ).
Proof.
intros cm rm tr attr t col Hcolrefs_rm.
destruct rm.
unfold getColumnReference in Hcolrefs_rm.
simpl.
simpl in Hcolrefs_rm.
clear tr.
rename modelLinks into rm_links.
induction rm_links.
- done.
- destruct a.
  destruct reer_arg.
  - simpl in Hcolrefs_rm.
    simpl.
    right. apply IHrm_links. done.
  - simpl.
    destruct r.
    destruct (beq_Column c col) eqn: ca.
    - simpl in Hcolrefs_rm.
      rewrite ca in Hcolrefs_rm.
      left.
      inversion Hcolrefs_rm.
      assert (c = col). { apply lem_beq_Column_id. done. }   
      rewrite H.
      done.
    - right.
      apply IHrm_links.
      simpl in Hcolrefs_rm.
      rewrite ca in Hcolrefs_rm.
      done. 
Qed.

Lemma lem_getTableColumns:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (c: Class) (t : Table) (cols: list Column),
     getTableColumns t rm = return cols ->
       (In (Build_RelationalMetamodel_ELink TableColumnsEReference (BuildTableColumns t cols)) (allModelLinks rm) )).
Proof.
intros cm rm tr c t cols Htcols_rm.
destruct rm.
unfold getTableColumns in Htcols_rm.
simpl.
simpl in Htcols_rm.
clear tr.
rename modelLinks into rm_links.
induction rm_links.
- done.
- destruct a.
  destruct reer_arg.
  - simpl.
    destruct r.
    destruct (beq_Table t0 t) eqn: ca.
    - simpl in Htcols_rm.
      rewrite ca in Htcols_rm.
      left.
      inversion Htcols_rm.
      assert (t0 = t). {apply lem_beq_Table_id. done. }  
      rewrite H.
      done.
    - right.
      apply IHrm_links.
      simpl in Htcols_rm.
      rewrite ca in Htcols_rm.
      done. 
  - simpl in Htcols_rm.
    simpl.
    right. apply IHrm_links. done. 
Qed.


Lemma lem_disagree_tableColums:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (c: Class) (t : Table) (cols: list Column),
     In (ClassMetamodel_toEObject c) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c::nil))) ->
     getClassAttributes c cm = None ->
     getTableColumns t rm = return cols -> 
     False
).
Proof.
  intros cm rm tr c t cols Hinc_c_cm Hinc_c_apply Hclass_attrs Htablecolumns_rm.
  (* simpl Hinc_c_apply *)
  unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hinc_c_apply.
  simpl in Hinc_c_apply.
  unfold setTableId in Hinc_c_apply.
  simpl in Hinc_c_apply.
  try destruct Hinc_c_apply; inversion H.
  clear H0. rename H into Hinc_c_apply.
  apply rel_invert in Hinc_c_apply.
  
  (* find sp corresponding to col_t2 *)
  assert (In (Build_RelationalMetamodel_ELink TableColumnsEReference (BuildTableColumns t cols)) (allModelLinks rm)).
  { apply (@lem_getTableColumns cm); auto. }

  rewrite tr in H.
  unfold execute in H.
  simpl in H.
  apply concat_map_option_exists in H.
  destruct H.
  destruct H.
  destruct (applyPattern Class2Relational cm x ) eqn: apply_res.
  + rename x into sp.
    rename H into Hinc_sp_cm.
    rename H0 into H1.
    destruct sp.
    - done.
    - destruct sp.
      --  destruct c0.
          destruct clec_arg.
          --- (* class  *)
              inversion apply_res.
              unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionToList in H0.
              simpl in H0.
              unfold setTableId in H0.
              simpl in H0.
              rewrite <- H0 in H1.
              destruct (getClassAttributes c0 cm) eqn: c1_ca.
              * simpl in H1.
                destruct H1.
                ** apply rel_elink_invert in H.
                  inversion H.
                  rewrite <- Hinc_c_apply in H2.
                  assert (c = c0). {inversion H2. destruct c, c0. simpl in H4, H5. repeat apply lem_string_app_inv_tail in H4. rewrite H4 H5. done. }
                  rewrite <- H1 in c1_ca.
                  rewrite Hclass_attrs in c1_ca.
                  done.
                ** done.
              * done.
          --- (* attribute impossible *)
              unfold applyPattern, matchPattern in apply_res.
              simpl in apply_res.
              destruct (getAttributeMultiValued c0) eqn: c1_ca.
              * done.
              * simpl in H1.
                simpl in apply_res.
                unfold instantiateRuleOnPattern, applyRuleOnPattern in apply_res.
                simpl in apply_res.
                rewrite c1_ca in apply_res.
                simpl in apply_res.
                unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression in apply_res.
                simpl in apply_res.
                unfold getAttributeType in apply_res.
                simpl in apply_res.
                unfold optionToList in apply_res.
                simpl in apply_res.
                destruct ( ClassMetamodel_getAttributeTypeOnLinks c0 (allModelLinks cm)) eqn: attr_type.
                **  inversion apply_res.
                    rewrite <- H0 in H1. 
                    crush. 
                    inversion H. 
                ** crush. 
       -- done.
   + done.
Qed.



Lemma lem_disagree_colrefs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t2 : Table) (col: Column),
     In (ClassMetamodel_toEObject a) (allModelElements cm) ->
     getAttributeMultiValued a = false ->
     In (RelationalMetamodel_toEObject col) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject a::nil))) ->
     getAttributeType a cm = None ->
     getColumnReference col rm = return t2 -> 
     False
).
Proof.
  intros cm rm tr attr t2 col Hinc_a_cm rl_attr_col_guard_ca Hinc_col_apply Hattr_type Hcolrefs_rm.
  (* simpl Hinc_col_apply *)
  unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hinc_col_apply.
  simpl in Hinc_col_apply.
  rewrite rl_attr_col_guard_ca in Hinc_col_apply.
  simpl in Hinc_col_apply.
  rewrite rl_attr_col_guard_ca in Hinc_col_apply.
  simpl in Hinc_col_apply.
  try destruct Hinc_col_apply; inversion H.
  clear H0. rename H into Hinc_col_apply.
  apply rel_invert in Hinc_col_apply.
  
  (* find sp corresponding to col_t2 *)
  assert (In (Build_RelationalMetamodel_ELink ColumnReferenceEReference (BuildColumnReference col t2)) (allModelLinks rm)).
  { apply (@lem_getColumnReference cm); auto. }

  rewrite tr in H.
  unfold execute in H.
  simpl in H.
  apply concat_map_option_exists in H.
  destruct H.
  destruct H.
  destruct (applyPattern Class2Relational cm x ) eqn: apply_res.
  + rename x into sp.
    rename H into Hinc_sp_cm.
    rename H0 into H1.
    destruct sp.
    - done.
    - destruct sp.
      --  destruct c.
          destruct clec_arg.
          --- (* class  *) 
              inversion apply_res.
              unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionToList in H0.
              simpl in H0.
              destruct (getClassAttributes c cm) eqn: c_ca.
              * crush.
                inversion H.
              * crush.
          --- (* attribute impossible *)
              unfold applyPattern, matchPattern in apply_res.
              simpl in apply_res.
              destruct (getAttributeMultiValued c) eqn: c1_ca.
              * done.
              * simpl in H1.
                simpl in apply_res.
                unfold instantiateRuleOnPattern, applyRuleOnPattern in apply_res.
                simpl in apply_res.
                rewrite c1_ca in apply_res.
                simpl in apply_res.
                unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression in apply_res.
                simpl in apply_res.
                unfold getAttributeType in apply_res.
                simpl in apply_res.
                unfold optionToList in apply_res.
                simpl in apply_res.
                destruct ( ClassMetamodel_getAttributeTypeOnLinks c (allModelLinks cm)) eqn: attr_type.
                **  inversion apply_res.
                    rewrite <- H0 in H1. 
                    destruct H1.
                    *** apply rel_elink_invert in H.
                        assert (c = attr). {
                          inversion H.
                          rewrite <- Hinc_col_apply in H2.
                          inversion H2.
                          repeat apply lem_string_app_inv_tail in H4.
                          destruct c, attr.
                          crush.
                        }
                        rewrite H1 in attr_type.
                        unfold getAttributeType in Hattr_type.
                        rewrite Hattr_type in attr_type.
                        inversion attr_type.
                        done.
                    *** crush.
                ** crush. 
       -- done.
   + done.
Qed.

Lemma lem_agree_colrefs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t1 t2 : Table) (col: Column),
     In (ClassMetamodel_toEObject a) (allModelElements cm) ->
     getAttributeMultiValued a = false ->
     In (RelationalMetamodel_toEObject col) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject a::nil))) ->
     RelationalMetamodel_getColumnReferenceOnLinks col (optionListToList (applyPattern Class2Relational cm (ClassMetamodel_toEObject a::nil))) = return t1 ->
     getColumnReference col rm = return t2 -> 
     t1 = t2
).
Proof.
intros cm rm tr attr t1 t2 col Hinc_a_cm rl_attr_col_guard_ca Hinc_col_apply Hcolrefs_sp Hcolrefs_rm.

(* simpl Hinc_col_apply *)
unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hinc_col_apply.
simpl in Hinc_col_apply.
rewrite rl_attr_col_guard_ca in Hinc_col_apply.
simpl in Hinc_col_apply.
rewrite rl_attr_col_guard_ca in Hinc_col_apply.
simpl in Hinc_col_apply.
try destruct Hinc_col_apply; inversion H.
clear H0. rename H into Hinc_col_apply.
apply rel_invert in Hinc_col_apply.


(* simpl Hcolrefs_sp *)
unfold applyPattern, matchPattern, matchRuleOnPattern,optionListToList in Hcolrefs_sp.
simpl in Hcolrefs_sp.
rewrite rl_attr_col_guard_ca in Hcolrefs_sp.
simpl in Hcolrefs_sp.
unfold instantiateRuleOnPattern, applyRuleOnPattern in Hcolrefs_sp.
simpl in Hcolrefs_sp.
rewrite rl_attr_col_guard_ca in Hcolrefs_sp.
simpl in Hcolrefs_sp.
unfold applyOutputPatternReferencesOnPattern, setTargetElementId, evalOutputBindingExpression in Hcolrefs_sp.
simpl in Hcolrefs_sp.

destruct (getAttributeType attr cm) eqn: attr_type_ca.
- simpl in Hcolrefs_sp.
  rewrite Hinc_col_apply in Hcolrefs_sp.
  assert (beq_Column col col = true). { apply lem_beq_Column_refl. }
  rewrite H in Hcolrefs_sp.
  inversion Hcolrefs_sp.
  
  (* find sp corresponding to col_t2 *)
  assert (In (Build_RelationalMetamodel_ELink ColumnReferenceEReference (BuildColumnReference col t2)) (allModelLinks rm)).
  { apply (@lem_getColumnReference cm); auto. }
  rewrite tr in H0.
  unfold execute in H0.
  simpl in H0.
  apply concat_map_option_exists in H0.
  destruct H0.
  destruct H0.
  rename x into sp.
  rename H0 into Hinc_sp_cm.
  rename H2 into H3.

  destruct (applyPattern Class2Relational cm sp) eqn: apply_res.
  -- destruct sp.
     --- done.
     --- destruct sp. 
      ---- destruct c0. destruct clec_arg.
            * (* class impossible *)
              inversion apply_res.
              rewrite <- H2 in H3.
              unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionList2List in H3.
              simpl in H3.
              destruct (getClassAttributes c0 cm) eqn: c_ca.
              * crush. done.
              * done.
            * (* attribute *)
                unfold applyPattern, matchPattern in apply_res.
                simpl in apply_res.
                destruct (getAttributeMultiValued c0) eqn: c1_ca.
                * done.
                * simpl in H1.
                  simpl in apply_res.
                  unfold instantiateRuleOnPattern, applyRuleOnPattern in apply_res.
                  simpl in apply_res.
                  rewrite c1_ca in apply_res.
                  simpl in apply_res.
                  unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression in apply_res.
                  simpl in apply_res.
                  unfold getAttributeType in apply_res.
                  simpl in apply_res.
                  unfold optionToList in apply_res.
                  simpl in apply_res.
                  destruct ( ClassMetamodel_getAttributeTypeOnLinks c0 (allModelLinks cm)) eqn: attr_type.
                  **  inversion apply_res.
                      rewrite <- H2 in H3. 
                      destruct H3.
                      *** apply rel_elink_invert in H0.
                          assert (c0 = attr). {
                            inversion H0.
                            rewrite <- Hinc_col_apply in H4.
                            inversion H4.
                            repeat apply lem_string_app_inv_tail in H6.
                            destruct c0, attr.
                            crush.
                          }
                          inversion H0.
                          rewrite H3 in attr_type.
                          unfold getAttributeType in attr_type_ca. 
                          crush. 
                      *** crush.
                  ** crush.
      ---- done.  
  -- done.
- done.
Qed.


Lemma lem_col_table_infer_attr_class:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (attr: Attribute) (col: Column) (cl : Class) (t: Table),
     In (ClassMetamodel_toEObject attr) (allModelElements cm) ->
     In (ClassMetamodel_toEObject cl) (allModelElements cm) -> 
     getAttributeMultiValued attr = false ->
     In (RelationalMetamodel_toEObject col) (allModelElements rm) ->
     In (RelationalMetamodel_toEObject t) (allModelElements rm) -> 
     In (RelationalMetamodel_toEObject col) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject attr::nil))) ->
     In (RelationalMetamodel_toEObject t) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject cl::nil))) ->
     getColumnReference col rm = return t -> 
     getAttributeType attr cm = return cl
).
Proof.
  intros cm rm tr attr col cl t.
  intros Hinc_attr_cm Hinc_cl_cm rl_attr_col_guard_ca Hinc_col_rm Hinc_t_rm.
  intros Hcol_cos_attr Ht_cos_cl Hcolref.



  (* simplify Hcol_cos_attr *)
  unfold instantiatePattern,instantiateRuleOnPattern,matchPattern, setTargetElementId in Hcol_cos_attr.
  simpl in Hcol_cos_attr.
  rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
  simpl in Hcol_cos_attr.
  rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
  simpl in Hcol_cos_attr.

  (* simplify Ht_cos_cl *)
  unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, setTargetElementId in Ht_cos_cl.
  simpl in Ht_cos_cl.


  destruct Hcol_cos_attr; destruct Ht_cos_cl.
  -   rename H into Hcol_cos_attr.
      rename H0 into Ht_cos_cl.
      remember (RelationalMetamodel_getColumnReferenceOnLinks col 
                (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject AttributeEClass attr])))) as tx.
      remember (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject AttributeEClass attr]))) as tls.
      assert (incl (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject AttributeEClass attr]))) (allModelLinks rm)).
      { apply (@lem_inc_tp_rm cm rm tr attr). done. } 
      rename Heqtls into Happly_attr.
      rename Heqtx into Happly_attr_colref.

      (* compute apply_attr_colref: links generated associated with attr *)
      rewrite Happly_attr in Happly_attr_colref.
      unfold applyPattern, matchPattern, matchRuleOnPattern in Happly_attr_colref.
      simpl in Happly_attr_colref.

      rewrite rl_attr_col_guard_ca in Happly_attr_colref.
      simpl in Happly_attr_colref.

      unfold applyRuleOnPattern in Happly_attr_colref.
      unfold instantiateRuleOnPattern in Happly_attr_colref.
      simpl in Happly_attr_colref.

      rewrite rl_attr_col_guard_ca in Happly_attr_colref.
      simpl in Happly_attr_colref.
      unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionToList in Happly_attr_colref.
      simpl in Happly_attr_colref.
      remember Happly_attr_colref as Happly_attr_colref'.
      clear HeqHapply_attr_colref'.
      destruct (getAttributeType attr cm ) eqn: attr_type_ca.
      --    (* Compute tx: table asscoiated with attr *)
            unfold RelationalMetamodel_getColumnReferenceOnLinks in Happly_attr_colref.
            simpl in Happly_attr_colref.
            apply rel_invert in  Hcol_cos_attr.
            rewrite  Hcol_cos_attr in Happly_attr_colref.
            simpl in Happly_attr_colref.
            assert (beq_Column col col).
            {  apply lem_beq_Column_refl. }
            rewrite H0 in Happly_attr_colref.
            remember (setTableId (BuildTable newId (getClassName c))
                                (String.append (String.append (getClassId c) "__") "0_0")) as tx2.
            remember ((optionToList
                              (return RelationalMetamodel_toELinkOfEReference ColumnReferenceEReference
                                        (BuildColumnReference
                                           (setColumnId (BuildColumn newId (getAttributeName attr))
                                              (String.append (String.append (getAttributeId attr) "__") "1_0")) tx2)) ++
                            nil) ++ nil) as tls'.
            assert (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject AttributeEClass attr])) = tls').
            {
              unfold applyPattern, matchPattern.
              simpl.
              rewrite rl_attr_col_guard_ca.
              simpl .
              unfold applyRuleOnPattern .
              unfold instantiateRuleOnPattern .
              simpl.
              rewrite rl_attr_col_guard_ca .
              simpl.
              unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionToList.
              crush.
            }
            simpl in Heqtls'.
            rewrite  Happly_attr_colref' in Happly_attr_colref.
            rewrite H1 in H.
            assert (tx2 = t). 
            { apply (@lem_agree_colrefs cm rm tr attr tx2 t col); auto.
              - unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, matchRuleOnPattern, setTargetElementId. 
                simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. rewrite Hcol_cos_attr. done.
              - rewrite H1. done.
            }
            assert (cl = c).
            { try apply (@eq_class_table cm rm tr t tx2); auto; unfold instantiatePattern; unfold matchPattern; simpl.
              - left. done.
              - left. rewrite Heqtx2. unfold setTargetElementId. simpl. unfold setTableId. simpl. done.
            }
            rewrite H3.
            done.
      --    unfold RelationalMetamodel_getColumnReferenceOnLinks in Happly_attr_colref.
            simpl in Happly_attr_colref.
            apply rel_invert in  Hcol_cos_attr.
            
            simpl in Happly_attr_colref.
            assert False. {
              try apply (@lem_disagree_colrefs cm rm tr attr t col); auto.
              - unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, setTargetElementId. 
                simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. rewrite Hcol_cos_attr. done.
            }
            done.
  - done.
  - done.
  - done.
Qed.


Lemma lem_agree_tablecolumns:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (cl: Class) (cols1 cols2 : list Column) (t: Table),
     In (ClassMetamodel_toEObject cl) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject cl::nil))) ->
     getTableColumns t rm = return cols1 -> 
     RelationalMetamodel_getTableColumnsOnLinks t (optionListToList (applyPattern Class2Relational cm (ClassMetamodel_toEObject cl::nil))) = return cols2 ->
     cols1 = cols2
).
Proof.
  intros cm rm tr cl cols1 cols2 t Hinc_cl_cm Hinc_t_apply Htcols_rm Htcols_sp.

  (* simpl Hinc_col_apply *)
  unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hinc_t_apply.
  simpl in Hinc_t_apply.
  try destruct Hinc_t_apply; inversion H.
  clear H0. rename H into Hinc_t_apply.
  apply rel_invert in Hinc_t_apply.

  (* simpl Htcols_sp *)
  unfold applyPattern, matchPattern, matchRuleOnPattern,optionListToList in Htcols_sp.
  simpl in Htcols_sp.
  unfold instantiateRuleOnPattern, applyRuleOnPattern, applyOutputPatternReferencesOnPattern in Htcols_sp.
  simpl in Htcols_sp.
  unfold setTargetElementId, evalOutputBindingExpression in Htcols_sp.
  simpl in Htcols_sp.

  destruct (getClassAttributes cl cm) eqn: cl_attrs_ca.
  - simpl in Htcols_sp.
    rewrite Hinc_t_apply in Htcols_sp.
    assert (beq_Table t t = true). { apply lem_beq_Table_refl. }
    rewrite H in Htcols_sp.
    inversion Htcols_sp.

    (* find sp corresponding to col_t2 *)
    assert (In (Build_RelationalMetamodel_ELink TableColumnsEReference (BuildTableColumns t cols1)) (allModelLinks rm)).
    { apply (@lem_getTableColumns cm); auto. }
    rewrite tr in H0.
    unfold execute in H0.
    simpl in H0.
    apply concat_map_option_exists in H0.
    destruct H0.
    destruct H0.

    rename x into sp.
    rename H0 into Hinc_sp_cm.
    rename H2 into H3.


    destruct (applyPattern Class2Relational cm sp) eqn: apply_res.
    --   destruct sp.
          --- done.
          --- destruct sp.
              * destruct c.
                destruct clec_arg.
                ** (* class *)
                  inversion apply_res.
                  rewrite <- H2 in H3.
                  unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionList2List in H3.
                  simpl in H3.
                  destruct (getClassAttributes c cm) eqn: c_ca.
                  *** simpl in H3.
                      destruct H3.
                      ****  apply rel_elink_invert in H0.
                            assert (cl = c). {
                              inversion H0.
                              rewrite <- Hinc_t_apply in H4.
                              inversion H4.
                              destruct cl, c.
                              simpl in H6, H7.
                              repeat apply lem_string_app_inv_tail in H6.
                              rewrite H6 H7.
                              done.
                            }
                            inversion H0.
                            simpl.
                            assert (l=l1). { crush. }
                            rewrite H4.
                            done.
                      **** done.
                  *** done.
                ** (* attribute *)
                  unfold applyPattern, matchPattern in apply_res.
                  simpl in apply_res.
                  destruct (getAttributeMultiValued c) eqn: c1_ca.
                  *** done.
                  *** simpl in apply_res.
                      unfold instantiateRuleOnPattern, applyRuleOnPattern in apply_res.
                      simpl in apply_res.
                      rewrite c1_ca in apply_res.
                      simpl in apply_res.
                      unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression in apply_res.
                      simpl in apply_res.
                      unfold getAttributeType in apply_res.
                      simpl in apply_res.
                      unfold optionToList in apply_res.
                      simpl in apply_res.
                      destruct (ClassMetamodel_getAttributeTypeOnLinks) eqn:c1_type_ca.
                      ****  simpl in apply_res.
                            inversion apply_res.
                            rewrite <- H2 in H3. 
                            destruct H3.
                            + inversion H0.
                            + done.
                      ****  crush.
              * done.
    -- done.
  - done. 
Qed.





Lemma lem_table_cols_infer_class_attrs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (cl: Class) (attr: Attribute) (t: Table) (col: Column) (cl_attrs: list Attribute) (t_cols: list Column),
     In (ClassMetamodel_toEObject attr) (allModelElements cm) ->
     In (ClassMetamodel_toEObject cl) (allModelElements cm) -> 
     getAttributeMultiValued attr = false ->
     In (RelationalMetamodel_toEObject col) (allModelElements rm) ->
     In (RelationalMetamodel_toEObject t) (allModelElements rm) -> 
     In (RelationalMetamodel_toEObject col) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject attr::nil))) ->
     In (RelationalMetamodel_toEObject t) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject cl::nil))) ->
     (getClassAttributes cl cm) = Some cl_attrs ->
     (getTableColumns t rm) = Some t_cols ->
     In col t_cols -> 
     In attr cl_attrs
).
Proof.
intros cm rm tr cl attr t col cl_attrs t_cols Hinc_c1_cm Hinc_c2_cm rl_attr_col_guard_ca Hinc_col_rm Hinc_t_rm.
intros Hcol_cos_attr Ht_cos_cl Hcl_attrs Ht_cols Hcol_inc_t_cols.

(* simplify Hcol_cos_attr *)
unfold instantiatePattern,instantiateRuleOnPattern,matchPattern, setTargetElementId in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.


  (* simplify Ht_cos_cl *)
  unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, setTargetElementId in Ht_cos_cl.
  simpl in Ht_cos_cl.

destruct Hcol_cos_attr; destruct Ht_cos_cl. 
- {
    rename H into Hcol_cos_attr.
    rename H0 into Ht_cos_cl.
    remember (RelationalMetamodel_getTableColumnsOnLinks t 
                (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject ClassEClass cl])))) as t_cols'.
    remember (optionListToList (applyPattern Class2Relational cm ([Build_ClassMetamodel_EObject ClassEClass cl]))) as tm'.
    rename Heqt_cols' into Ht_cols'.
    symmetry in Ht_cols'.

    apply rel_invert in  Ht_cos_cl.
    apply rel_invert in  Hcol_cos_attr.


    (* compute apply_attr_colref: links generated associated with attr *)
    rewrite Heqtm' in Ht_cols'.
    unfold applyPattern, matchPattern, matchRuleOnPattern in Ht_cols'.
    simpl in Ht_cols'.


    unfold applyOutputPatternReferencesOnPattern, evalOutputBindingExpression, setTargetElementId, optionToList in Ht_cols'.
    simpl in Ht_cols'.

    assert (Some t_cols = t_cols'). { 
      destruct t_cols' eqn: t_cols'_ca.
       -  rename l into t_cols2.
         assert ( t_cols = t_cols2). {
         apply (@lem_agree_tablecolumns cm rm tr cl t_cols t_cols2 t); auto.
                - unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, matchRuleOnPattern, setTargetElementId. 
                  simpl.  left. rewrite Ht_cos_cl. done.
         }
         rewrite H. done.
      - rewrite Hcl_attrs in Ht_cols'. simpl in Ht_cols'. rewrite  Ht_cos_cl in Ht_cols'.
        simpl in Ht_cols'. assert (beq_Table t t = true). { apply lem_beq_Table_refl. }
        rewrite H in Ht_cols'. done.
    }
    rename H into H0.

    (* Compute tx: table asscoiated with attr *)
    rewrite Hcl_attrs in Ht_cols'. simpl in Ht_cols'.
    
    rewrite  Ht_cos_cl in Ht_cols'.
    simpl in Ht_cols'.
    assert (beq_Table t t = true). { apply lem_beq_Table_refl. }
    rewrite H in Ht_cols'.
    rewrite <- H0 in Ht_cols'.
    inversion Ht_cols'.
    
    rewrite <- H2 in Hcol_inc_t_cols.
    rewrite <- Hcol_cos_attr in Hcol_inc_t_cols.
    simpl in Hcol_inc_t_cols.

    clear H2 Ht_cols'.

    clear Hcl_attrs.
    induction cl_attrs.
    - done.
    - unfold setColumnId in Hcol_inc_t_cols.
      unfold resolve, resolveFix, matchPattern in Hcol_inc_t_cols.
      simpl in Hcol_inc_t_cols.
      destruct (~~ getAttributeMultiValued a) eqn:a_guard_ca.
      - simpl.
        destruct Hcol_inc_t_cols.
        + left. inversion H1. destruct a, attr. simpl in H3, H4. 
          simpl in rl_attr_col_guard_ca, a_guard_ca. apply negbTE  in a_guard_ca. 
          rewrite <- rl_attr_col_guard_ca in a_guard_ca. repeat apply lem_string_app_inv_tail in H3. crush. 
        + right. apply IHcl_attrs. done.
      - simpl in Hcol_inc_t_cols. right. apply IHcl_attrs. done.
  }
- done.
- done.
- done.

Qed.

Lemma lem_reach_step:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (t1 t2 : Table) (c1 c2: Class),
     In (ClassMetamodel_toEObject c1) (allModelElements cm) ->
     In (ClassMetamodel_toEObject c2) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t1) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c1::nil))) ->
     In (RelationalMetamodel_toEObject t2) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c2::nil))) ->
     reachable_table_step rm t1 t2 ->
     reachable_class_step cm c1 c2
 ).
Proof.
intros cm rm tr t1 t2 c1 c2 Hinc_c1_cm Hinc_c2_cm Hinc_t1_sp1 Hinc_t2_sp2 Hreach_t1_t2.
unfold reachable_table_step in Hreach_t1_t2.
decompose [and] Hreach_t1_t2. rename H into Hinc_t1_rm. rename H1 into Hinc_t2_rm. rename H2 into Hreach_table. clear Hreach_t1_t2.
unfold reachable_class_step.
split.
+ done.
+ split.
  ++ done.
  ++ destruct (getTableColumns t1 rm) eqn:table_coloumns_ca.
     rename l into t1_cols.
    +++ destruct (getClassAttributes c1 cm) eqn:class_attributes_ca.
        rename l into c1_attrs.
      ++++ (* getTableColumns x rm = l0 and getClassAttributes c1 cm = l1 *)
            destruct Hreach_table as [col].
            decompose [and] H. clear H. rename H0 into Hinc_col_rm. rename H2 into Hinc_col_t1cols. rename H3 into Heq_t2_colRef.
            remember tr as tr'.
            clear Heqtr'.
            apply tr_surj_elements with (t1:=col) in tr'.
            - destruct tr' as [sp_attr]. destruct H as [tp_col]. 
              destruct H as [Hattr_insp].
              destruct H as [Hcol_intp]. 
              destruct H as [Hinctp_rm].
              rename H into Hexec_rl_attr_col. 
              destruct sp_attr eqn:sp_attr_ca.
              -- inversion Hexec_rl_attr_col.
              -- rename c into attr_eo. rename l into sp_attr'.
                 destruct sp_attr' eqn:sp_attr'_ca. 
                 --- destruct attr_eo eqn:attr_eo_ca.
                     destruct clec_arg eqn:attr_Etype_ca; rename c into attr.
                     *  { (* attr is Class, impossible *) 
                           unfold instantiatePattern, instantiateRuleOnPattern, setTargetElementId in Hexec_rl_attr_col. 
                           simpl in Hexec_rl_attr_col.
                           inversion Hexec_rl_attr_col.
                           rewrite <- H0 in Hcol_intp.
                           simpl in Hcol_intp.
                           try destruct Hcol_intp; done.
                        }
                     *  { (* attr is Attribute *) 
                         destruct (getAttributeMultiValued attr) eqn:rl_attr_col_guard_ca.
                         **  (* getAttributeDerived attr = true *)
                              unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_rl_attr_col.
                              simpl in Hexec_rl_attr_col.
                              rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
                              simpl in Hexec_rl_attr_col.
                              done.
                         **  (* getAttributeDerived attr = false *)
                              unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_rl_attr_col.
                              simpl in Hexec_rl_attr_col.
                              repeat rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
                              simpl in Hexec_rl_attr_col.
                              rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
                              simpl in Hexec_rl_attr_col.
                              inversion Hexec_rl_attr_col.
                              rewrite <- H0 in Hcol_intp.
                              simpl in Hcol_intp.
                              destruct Hcol_intp.
                              ***  exists attr.
                                   repeat split.
                                    *** { (* In (ClassMetamodel_toEObject attr) (allModelElements cm) *)
                                          unfold incl in Hattr_insp.
                                          simpl in Hattr_insp.
                                          pose (Hattr_insp (ClassMetamodel_toEObject attr)) as Hinc_attr.
                                          apply Hinc_attr.
                                          left.
                                          done. 
                                        }
                                    *** { (* In attr c1_attrs *)
                                           apply (@lem_table_cols_infer_class_attrs cm rm tr c1 attr t1 col c1_attrs t1_cols); auto.
                                          - unfold incl in Hattr_insp. apply Hattr_insp. simpl. left. done. 
                                          - unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, setTargetElementId. 
                                            simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. done.
                                        }
                                    *** { (* getAttributeType attr cm = return c2 *)
                                          try apply (@lem_col_table_infer_attr_class cm rm tr attr col c2 t2); auto.
                                          - unfold incl in Hattr_insp. apply Hattr_insp. simpl. left. done. 
                                          - unfold instantiatePattern,instantiateRuleOnPattern, matchPattern, setTargetElementId. 
                                            simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. done.
                                        }
                              *** done.
                         } 
                 --- done.
            - done.
      ++++  (* getTableColumns t1 rm = l0 and getClassAttributes c1 cm = None, Impossible *)
            assert False. { apply (@lem_disagree_tableColums cm rm tr c1 t1 t1_cols); auto. }
            done.
  +++ done.
Qed.

Lemma lem_reach:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (t1 t2 : Table) (c1 c2: Class),
     In (ClassMetamodel_toEObject c1) (allModelElements cm) ->
     In (ClassMetamodel_toEObject c2) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t1) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c1::nil))) ->
     In (RelationalMetamodel_toEObject t2) (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c2::nil))) ->
     ReachableTable rm t1 t2 ->
     ReachableClass cm c1 c2
 ).
Proof.
  intros cm rm H t1 t2 c1 c2 Hinc_c1_cm Hinc_c2_cm Hinc_t1_sp1 Hinc_t2_sp2 Hreach_t1_t2.
  generalize dependent c1.
  induction Hreach_t1_t2.
  - intros.
    assert (c1 = c2). { try apply (eq_class_table cm rm H x x); auto. }
    rewrite H0.
    apply reachable_class_refl.
  - intros.
    remember H as tr.
    clear Heqtr.
    apply tr_surj_elements with (t1:=y) in H.
    --  destruct H as [sp_attr]. destruct H as [tp_col]. 
        destruct H as [Hattr_insp].
        destruct H as [Hcol_intp]. 
        destruct H as [Hinctp_rm].
        rename H into Hexec_rl_attr_col. 
        destruct sp_attr eqn:sp_attr_ca; inversion Hexec_rl_attr_col.
        destruct l eqn:l_ca; inversion Hexec_rl_attr_col. clear H2.
        destruct c eqn:c_ca.
        destruct clec_arg eqn:clec_arg_ca; rename c0 into c3.
      * (* clec_arg_ca = ClassEClass *)
        apply IHHreach_t1_t2 with (c1:=c3) in Hinc_t2_sp2. 
        ** (* reachable_table_column_step x y -> reachable_class_step cm c1 c3 *)
           assert (reachable_class_step cm c1 c3). 
           {
            try apply (@lem_reach_step cm rm tr x y); auto.
            - unfold incl in Hattr_insp. apply Hattr_insp. simpl. left. done.
            - inversion Hexec_rl_attr_col. rewrite <- H2 in Hcol_intp. 
              simpl in Hcol_intp.
              crush.
           }
           apply reachable_class_trans with c3.
           *** exact. 
           *** exact.
        ** unfold incl in Hattr_insp.
           simpl in Hattr_insp.
           rewrite <- c_ca in Hattr_insp.
           pose (Hattr_insp (ClassMetamodel_toEObject c3)) as Hinc.
           apply Hinc.
           left.
           done.
        ** inversion Hexec_rl_attr_col. rewrite <- H2 in Hcol_intp. 
           simpl in Hcol_intp.
           crush.
      *  (* clec_arg_ca = AttributeEClass, impoosible *)   
         destruct (getAttributeMultiValued c3) eqn:rl_attr_col_guard_ca.
         **  (* getAttributeDerived attr = true *)
              unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_rl_attr_col.
              simpl in Hexec_rl_attr_col.
              rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
              simpl in Hexec_rl_attr_col.
              done.
         **  (* getAttributeDerived attr = false *)
              unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_rl_attr_col.
              simpl in Hexec_rl_attr_col.
              repeat rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
              simpl in Hexec_rl_attr_col.
              rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col.
              simpl in Hexec_rl_attr_col.
              inversion Hexec_rl_attr_col.
              rewrite <- H2 in Hcol_intp.
              simpl in Hcol_intp.
              destruct Hcol_intp; done.
    --  unfold reachable_table_step in H0.
        destruct H0. destruct H1. 
        assumption.
Qed.

(* try cast x to type t, if succ and results x1, do e1, else do e2 *)
Notation "x1 <= [[ t ]] x | 'SUCC' e1 'FAIL' e2" :=
(match toModelClass t x with
| Some x1 => e1
| None => e2
end)
  (right associativity, at level 70).

Definition Trivial := True.

Fixpoint ClassModel_fistClass' (l : list ClassMetamodel_EObject) : option Class :=
 match l with
  | x::l' => match ClassMetamodel_instanceOfEClass ClassEClass x with
               | true => ClassMetamodel_toEClass ClassEClass x
               | false => ClassModel_fistClass' l'
            end
  | _ => None
 end.

Definition ClassModel_fistClass (cm: ClassModel) := ClassModel_fistClass' (allModelElements cm).

Lemma lemma_ClassModel_fistClass_inc:
 forall (cm : ClassModel) (c: Class),
  ClassModel_fistClass cm = Some c -> In (ClassMetamodel_toEObject c) (allModelElements cm). 
Proof.
intros cm c res.
unfold ClassModel_fistClass, ClassModel_fistClass' in res.
destruct cm.
simpl in res. simpl.
induction modelElements.
- done.
- destruct (ClassMetamodel_instanceOfEClass ClassEClass a) eqn: ca.
  - destruct a.
    destruct clec_arg.
    - simpl in res.
      inversion res.
      simpl. left.
      done.
    - done.
  - simpl.
    right.
    apply IHmodelElements.
    done.
Qed.

(* if none of reachable classes from [firstClass] named "Bad"
   then none of reachable tables from [firstTable] (gen from [firstClass]) named "Bad"
 *)
Theorem Class2Relational_keeps_full_reachability :
  forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
    match (ClassModel_fistClass cm) with
     | Some c1 => 
        (~ (beq_string (getClassName c1) "Bad"))                                                                                                           -> (* pre *)
        (forall (c2 : Class), In (ClassMetamodel_toEObject c2) (allModelElements cm) -> ReachableClass cm c1 c2 -> ~ (beq_string (getClassName c2) "Bad")) -> (* pre *)
         (forall (t: RelationalMetamodel_EObject),
           In t (allModelElements rm) ->
           In t (optionListToList (instantiatePattern Class2Relational cm (ClassMetamodel_toEObject c1::nil))) ->
           (t1 <= [[TableEClass]] t  | 
             SUCC (forall (t2 : Table), In (RelationalMetamodel_toEObject t2) (allModelElements rm) -> ReachableTable rm t1 t2 ->
                    ~ (beq_string (getTableName t2) "Bad"))                                                                                                  (* post *)
             FAIL Trivial)
         )
         
     | None => Trivial
    end.  
Proof.
  intros cm rm tr .
  destruct (ClassModel_fistClass cm) eqn: first_Class_ca.
  - intros Hgood_class Hreach_class t Hinc_t Hinc_t_rl.
    destruct (toModelClass TableEClass t) as [t1|] eqn: cast_ca.
     - intros t2 Hinc_t2 Hreach_t_t2.
       simpl in t1.
       (* important here *)
       induction Hreach_t_t2.
       - (* reachable_table_refl *)
         destruct Hinc_t_rl.
         - unfold RelationalMetamodel_toEObject in H.
           rewrite <- H in cast_ca.
           simpl in cast_ca. 
           inversion cast_ca.
           done.
         - done.
       - (* reachable_table_trans *)
           (* get corresponding eobject c of Table z *)
         - remember tr as tr'.
           clear  Heqtr' .
           apply tr_surj_elements with (t1:=z) in tr'.
           +  destruct tr' as [sp_z]. destruct H0 as [tp_z]. 
              destruct H0 as [Hinclsp_z].
              destruct H0 as [Hintp_z]. 
              destruct H0 as [incltp_z].
              rename H0 into Hexec_z. 
              destruct sp_z eqn:sp_z_ca; inversion Hexec_z.
              destruct l eqn:l_ca; inversion Hexec_z. clear H1 H2.
              destruct c0 eqn:c0_z_ca.
              destruct clec_arg eqn:clec_arg_ca.

              (* if c is Class, Important *)
               * inversion Hexec_z.
                   rewrite <- H1 in Hintp_z.
                   simpl in Hintp_z.
                   destruct Hintp_z; auto.
                   ** assert (In c0 ([Build_ClassMetamodel_EObject ClassEClass c1])). {
                         simpl. left. symmetry. assumption.
                      }
                      apply Hinclsp_z in H2.
                      rewrite c0_z_ca in H2.
                      apply Hreach_class in H2.
                      - simpl in H.
                        apply rel_invert in H0.
                        rewrite <- H0.
                        done.
                      - try apply (@lem_reach cm rm tr x z c c1); auto.
                        - apply (lemma_ClassModel_fistClass_inc); done.
                        - crush.
                        - simpl. left. done.
                        - apply (@reachable_table_trans rm x y z H Hreach_t_t2). 
              (* if c is Attribute, Trivial *)
               * destruct (getAttributeMultiValued c1) eqn:rl_attr_col_guard_ca.
                 **  (* getAttributeDerived attr = true *)
                      unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_z.
                      simpl in Hexec_z.
                      rewrite rl_attr_col_guard_ca in Hexec_z.
                      simpl in Hexec_z.
                      done.
                 **  (* getAttributeDerived attr = false *)
                      unfold instantiatePattern, instantiateRuleOnPattern, matchPattern, setTargetElementId in Hexec_z.
                      simpl in Hexec_z.
                      repeat rewrite rl_attr_col_guard_ca in Hexec_z.
                      simpl in Hexec_z.
                      rewrite rl_attr_col_guard_ca in Hexec_z.
                      simpl in Hexec_z.
                      inversion Hexec_z.
                      rewrite <- H1 in Hintp_z.
                      simpl in Hintp_z.
                      destruct Hintp_z; done.
           + done.
     - done.
  - done.
Qed.

