Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Arith.EqNat.
Require Import List.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype.  

Require Import core.utils.Utils_Top.
Require Import core.CoqTL.

Require Import example.Class2Relational.
Require Import example.ClassMetamodel.
Require Import example.RelationalMetamodel.









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
     incl (applyPattern (getRules' Class2Relational cm) (ClassMetamodel_toEObject a::nil)) (allModelLinks rm)).
Proof.
intros cm rm tr attr Hinc_attr_cm attr_guard_ca.
rewrite tr. simpl.
apply concat_map_incl.
assert (In (ClassMetamodel_toEObject attr::nil) (allTuples Class2Relational cm)).
{ 
  unfold allTuples.
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
      apply IHl.
      done.
 }
assumption.
Qed.









Lemma lem_getColumnReference:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t : Table) (col: Column),
     getColumnReference col rm = return t ->
       In (RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference col t)) (allModelLinks rm) ).
Proof.
intros cm rm tr attr t col Hcolrefs_rm.
destruct rm.
unfold getColumnReference in Hcolrefs_rm.
simpl.
simpl in Hcolrefs_rm.
clear tr.
rename l0 into rm_links.
induction rm_links.
- done.
- destruct a.
  destruct c.
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
       (In (RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns t cols)) (allModelLinks rm) )).
Proof.
intros cm rm tr c t cols Htcols_rm.
destruct rm.
unfold getTableColumns in Htcols_rm.
simpl.
simpl in Htcols_rm.
clear tr.
rename l0 into rm_links.
induction rm_links.
- done.
- destruct a.
  destruct c0.
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
     In (RelationalMetamodel_toEObject t) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c::nil)) ->
     getClassAttributes c cm = None ->
     getTableColumns t rm = return cols -> 
     False
).
Proof.
  intros cm rm tr c t cols Hinc_c_cm Hinc_c_apply Hclass_attrs Htablecolumns_rm.
  (* simpl Hinc_c_apply *)
  unfold instantiatePattern, instantiateRuleOnPattern, executeRuleOnPattern in Hinc_c_apply.
  simpl in Hinc_c_apply.
  try destruct Hinc_c_apply; inversion H.
  clear H0. rename H into Hinc_c_apply.
  apply rel_invert in Hinc_c_apply.
  
  (* find sp corresponding to col_t2 *)
  assert (In (RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns t cols)) (allModelLinks rm)).
  { apply (@lem_getTableColumns cm); auto. }

  rewrite tr in H.
  unfold execute in H.
  simpl in H.
  apply concat_map_exists in H.
  destruct H.
  destruct H.

  rename x into sp.
  rename H into Hinc_sp_cm.
  rename H0 into H1.
  destruct sp.
  - done.
  - destruct sp.
    - destruct c0.
      destruct c0.
      - (* class  *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern in H1.
        simpl in H1.
        destruct (getClassAttributes c1 cm) eqn: c1_ca.
        - simpl in H1.
          destruct H1.
          - apply rel_elink_invert in H.
            inversion H.
            rewrite <- Hinc_c_apply in H1.
            clear H H2.
            assert (c = c1). {inversion H1. destruct c, c1. simpl in H0, H2. rewrite H0 H2. done. }
            rewrite <- H in c1_ca.
            rewrite Hclass_attrs in c1_ca.
            done.
          - done.
        - done.
      - (* attribute impossible *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern in H1.
        simpl in H1.
        destruct (getAttributeDerived c1) eqn: c1_ca.
        - done.
        - simpl in H1.
          rewrite c1_ca in H1. simpl in H1.
          unfold getAllOuputPatternElementLinks in H1.
          simpl in H1.
          destruct (getAttributeType c1 cm) eqn:c1_type_ca.
          - simpl in H1.
            destruct H1.
            - done.
            - done.
          - done.
   - done.
Qed.


Lemma lem_disagree_colrefs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t2 : Table) (col: Column),
     In (ClassMetamodel_toEObject a) (allModelElements cm) ->
     getAttributeDerived a = false ->
     In (RelationalMetamodel_toEObject col) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject a::nil)) ->
     getAttributeType a cm = None ->
     getColumnReference col rm = return t2 -> 
     False
).
Proof.
  intros cm rm tr attr t2 col Hinc_a_cm rl_attr_col_guard_ca Hinc_col_apply Hattr_type Hcolrefs_rm.
  (* simpl Hinc_col_apply *)
  unfold instantiatePattern, instantiateRuleOnPattern, executeRuleOnPattern in Hinc_col_apply.
  simpl in Hinc_col_apply.
  rewrite rl_attr_col_guard_ca in Hinc_col_apply.
  simpl in Hinc_col_apply.
  rewrite rl_attr_col_guard_ca in Hinc_col_apply.
  simpl in Hinc_col_apply.
  try destruct Hinc_col_apply; inversion H.
  clear H0. rename H into Hinc_col_apply.
  apply rel_invert in Hinc_col_apply.
  
  (* find sp corresponding to col_t2 *)
  assert (In (RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference col t2)) (allModelLinks rm)).
  { apply (@lem_getColumnReference cm); auto. }

  rewrite tr in H.
  unfold execute in H.
  simpl in H.
  apply concat_map_exists in H.
  destruct H.
  destruct H.

  rename x into sp.
  rename H into Hinc_sp_cm.
  rename H0 into H1.
  destruct sp.
  - done.
  - destruct sp.
    - destruct c.
      destruct c.
      - (* class impossible *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern,getAllOuputPatternElementLinks in H1.
        simpl in H1.
        destruct (getClassAttributes c0 cm) eqn: c1_ca.
        - simpl in H1.
          destruct H1.
          - done.
          - done.
        - done.
      - (* attribute *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern in H1.
        simpl in H1.
        destruct (getAttributeDerived c0) eqn: c1_ca.
        - done.
        - simpl in H1.
          rewrite c1_ca in H1. simpl in H1.
          unfold getAllOuputPatternElementLinks in H1.
          simpl in H1.
          destruct (getAttributeType c0 cm) eqn:c1_type_ca.
          - simpl in H1.
            destruct H1.
            - apply rel_elink_invert in H.
              assert (c0 = attr). {
                inversion H. 
                rewrite <- Hinc_col_apply in H1.
                inversion H1.
                destruct c0, attr.
                simpl in H3, H4, c1_ca, rl_attr_col_guard_ca.
                rewrite H3.
                rewrite H4.
                rewrite c1_ca.
                rewrite rl_attr_col_guard_ca.
                done. 
              }
              inversion H0.
              rewrite H1 in c1_type_ca.
              rewrite Hattr_type in c1_type_ca.
              inversion c1_type_ca.
              done.
            - done.
          - done.
Qed.

Lemma lem_agree_colrefs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (a: Attribute) (t1 t2 : Table) (col: Column),
     In (ClassMetamodel_toEObject a) (allModelElements cm) ->
     getAttributeDerived a = false ->
     In (RelationalMetamodel_toEObject col) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject a::nil)) ->
     getColumnReferenceOnLinks col (applyPattern (getRules' Class2Relational cm) (ClassMetamodel_toEObject a::nil)) = return t1 ->
     getColumnReference col rm = return t2 -> 
     t1 = t2
).
Proof.
intros cm rm tr attr t1 t2 col Hinc_a_cm rl_attr_col_guard_ca Hinc_col_apply Hcolrefs_sp Hcolrefs_rm.

(* simpl Hinc_col_apply *)
unfold instantiatePattern, instantiateRuleOnPattern, executeRuleOnPattern in Hinc_col_apply.
simpl in Hinc_col_apply.
rewrite rl_attr_col_guard_ca in Hinc_col_apply.
simpl in Hinc_col_apply.
rewrite rl_attr_col_guard_ca in Hinc_col_apply.
simpl in Hinc_col_apply.
try destruct Hinc_col_apply; inversion H.
clear H0. rename H into Hinc_col_apply.
apply rel_invert in Hinc_col_apply.

(* simpl Hcolrefs_sp *)
unfold applyPattern in Hcolrefs_sp.
simpl in Hcolrefs_sp.
rewrite rl_attr_col_guard_ca in Hcolrefs_sp.
simpl in Hcolrefs_sp.
unfold applyRuleOnPattern in Hcolrefs_sp.
unfold executeRuleOnPattern in Hcolrefs_sp.
simpl in Hcolrefs_sp.
rewrite rl_attr_col_guard_ca in Hcolrefs_sp.
simpl in Hcolrefs_sp.
unfold getAllOuputPatternElementLinks in Hcolrefs_sp.
simpl in Hcolrefs_sp.

destruct (getAttributeType attr cm) eqn: attr_type_ca.
- simpl in Hcolrefs_sp.
  rewrite Hinc_col_apply in Hcolrefs_sp.
  assert (beq_Column col col = true). { apply lem_beq_Column_refl. }
  rewrite H in Hcolrefs_sp.
  inversion Hcolrefs_sp.
  
  (* find sp corresponding to col_t2 *)
  assert (In (RelationalMetamodel_BuildELink ColumnReferenceReference (BuildColumnReference col t2)) (allModelLinks rm)).
  { apply (@lem_getColumnReference cm); auto. }
  rewrite tr in H0.
  unfold execute in H0.
  simpl in H0.
  apply concat_map_exists in H0.
  destruct H0.
  destruct H0.
  
  rename x into sp.
  rename H0 into Hinc_sp_cm.
  rename H2 into H3.
  destruct sp.
  - done.
  - destruct sp.
    - destruct c0.
      destruct c0.
      - (* class impossible *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern,getAllOuputPatternElementLinks in H3.
        simpl in H3.
        destruct (getClassAttributes c1 cm) eqn: c1_ca.
        - simpl in H3.
          destruct H3.
          - done.
          - done.
        - done.
      - (* attribute *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern in H3.
        simpl in H3.
        destruct (getAttributeDerived c1) eqn: c1_ca.
        - done.
        - simpl in H3.
          rewrite c1_ca in H3. simpl in H3.
          unfold getAllOuputPatternElementLinks in H3.
          simpl in H3.
          destruct (getAttributeType c1 cm) eqn:c1_type_ca.
          - simpl in H3.
            destruct H3.
            - apply rel_elink_invert in H0.
              assert (c1 = attr). {
                inversion H0.
                rewrite <- Hinc_col_apply in H3.
                inversion H3.
                destruct c1, attr.
                simpl in H5, H6, c1_ca, rl_attr_col_guard_ca.
                rewrite H5.
                rewrite H6.
                rewrite c1_ca.
                rewrite rl_attr_col_guard_ca.
                done.
              }
              inversion H0.
              rewrite H2 in c1_type_ca.
              rewrite attr_type_ca in c1_type_ca.
              inversion c1_type_ca.
              rewrite <- H6.
              done.
            - done.
          - done.
        
    - done.
- done.
Qed.

Lemma eq_class_table:
  (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (t1 t2 : Table) (c1 c2: Class),
(*   TODO: Bugs in model construction prevent we have this.
     In (ClassMetamodel_toEObject c1) (allModelElements cm) ->
     In (ClassMetamodel_toEObject c2) (allModelElements cm) -> *)
     In (RelationalMetamodel_toEObject t1) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil)) ->
     In (RelationalMetamodel_toEObject t2) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c2::nil)) ->
     t1 = t2 ->
     c1 = c2).
Proof.
intros cm rm tr t1 t2 c1 c2  Hinc_t1_sp1 Hinc_t2_sp2 Heq_tables.
unfold instantiatePattern in Hinc_t1_sp1, Hinc_t2_sp2.
simpl in Hinc_t1_sp1, Hinc_t2_sp2.
try destruct Hinc_t1_sp1; destruct Hinc_t2_sp2; auto.
- rewrite Heq_tables in H.
  rewrite <- H in H0.
  apply rel_invert in H0.
  inversion H0.
  destruct c1, c2.
  simpl in H2, H3.
  rewrite H2.
  rewrite H3.
  done.
- done.
- done.
- done.
Qed.

Lemma lem_col_table_infer_attr_class:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (attr: Attribute) (col: Column) (cl : Class) (t: Table),
     In (ClassMetamodel_toEObject attr) (allModelElements cm) ->
     In (ClassMetamodel_toEObject cl) (allModelElements cm) -> 
     getAttributeDerived attr = false ->
     In (RelationalMetamodel_toEObject col) (allModelElements rm) ->
     In (RelationalMetamodel_toEObject t) (allModelElements rm) -> 
     In (RelationalMetamodel_toEObject col) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject attr::nil)) ->
     In (RelationalMetamodel_toEObject t) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject cl::nil)) ->
     getColumnReference col rm = return t -> 
     getAttributeType attr cm = return cl
).
Proof.
intros cm rm tr attr col cl t.
intros Hinc_attr_cm Hinc_cl_cm rl_attr_col_guard_ca Hinc_col_rm Hinc_t_rm.
intros Hcol_cos_attr Ht_cos_cl Hcolref.

(* simplify Hcol_cos_attr *)
unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.

(* simplify Ht_cos_cl *)
unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern in Ht_cos_cl.
simpl in Ht_cos_cl.


destruct Hcol_cos_attr; destruct Ht_cos_cl. 
- {
    rename H into Hcol_cos_attr.
    rename H0 into Ht_cos_cl.
    remember (getColumnReferenceOnLinks col 
              (applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject AttributeEClass attr]))) as tx.
    remember (applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject AttributeEClass attr])) as tls.
    assert (incl (applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject AttributeEClass attr])) (allModelLinks rm)).
    { apply (@lem_inc_tp_rm cm rm tr attr). done. } 
    rename Heqtls into Happly_attr.
    rename Heqtx into Happly_attr_colref.
    
    (* compute apply_attr_colref: links generated associated with attr *)
    rewrite Happly_attr in Happly_attr_colref.
    unfold applyPattern in Happly_attr_colref.
    simpl in Happly_attr_colref.

    rewrite rl_attr_col_guard_ca in Happly_attr_colref.
    simpl in Happly_attr_colref.

    unfold applyRuleOnPattern in Happly_attr_colref.
    unfold executeRuleOnPattern in Happly_attr_colref.
    simpl in Happly_attr_colref.

    rewrite rl_attr_col_guard_ca in Happly_attr_colref.
    simpl in Happly_attr_colref.
    unfold getAllOuputPatternElementLinks in Happly_attr_colref.
    simpl in Happly_attr_colref.
    remember Happly_attr_colref as Happly_attr_colref'.
    clear HeqHapply_attr_colref'.
    destruct (getAttributeType attr cm ) eqn: attr_type_ca.
    ****  (* Compute tx: table asscoiated with attr *)
          unfold getColumnReferenceOnLinks in Happly_attr_colref.
          simpl in Happly_attr_colref.
          apply rel_invert in  Hcol_cos_attr.
          rewrite  Hcol_cos_attr in Happly_attr_colref.
          simpl in Happly_attr_colref.
          destruct (beq_Column col col) eqn: g.
          - { remember (BuildTable (getClassId c) (getClassName c)) as tx2.
              remember ((([RelationalMetamodel_BuildELink ColumnReferenceReference
                       (BuildColumnReference
                          (BuildColumn (getAttributeId attr) (getAttributeName attr))
                          tx2)]) ++ nil)) as tls'.
              assert ((applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject AttributeEClass attr])) = tls').
              {
                unfold applyPattern .
                simpl.
                rewrite rl_attr_col_guard_ca.
                simpl .
                unfold applyRuleOnPattern .
                unfold executeRuleOnPattern .
                simpl.
                rewrite rl_attr_col_guard_ca .
                simpl.
                unfold getAllOuputPatternElementLinks .
                simpl .
                rewrite attr_type_ca.
                rewrite Heqtls'.
                rewrite Heqtx2.
                done.
              }
              simpl in Heqtls'.
              rewrite  Happly_attr_colref' in Happly_attr_colref.
              rewrite H0 in H.
              assert (tx2 = t). 
              { apply (@lem_agree_colrefs cm rm tr attr tx2 t col); auto.
                - unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern. 
                  simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. rewrite Hcol_cos_attr. done.
                - rewrite H0. done.
              }
              assert (cl = c).
              { try apply (@eq_class_table cm rm tr t tx2); auto; unfold instantiatePattern; unfold matchPattern; simpl.
                - left. done.
                - left. rewrite Heqtx2. done.
              }
              rewrite H2.
              done.
            }
          - destruct col. unfold beq_Column in g. simpl in g. 
            assert (true = PeanoNat.Nat.eqb n n). { apply beq_nat_refl. }
            rewrite <- H0 in g.
            simpl in g.
            assert (beq_string s s = true). { apply lem_beq_string_id. }
            rewrite H1 in g.
            done.                          
    ****  unfold getColumnReferenceOnLinks in Happly_attr_colref.
          simpl in Happly_attr_colref.
          apply rel_invert in  Hcol_cos_attr.
          
          simpl in Happly_attr_colref.
          assert False. {
            try apply (@lem_disagree_colrefs cm rm tr attr t col); auto.
            - unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern. 
              simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. rewrite Hcol_cos_attr. done.
          }
          done.
          
  }
- done.
- done.
- done.

Qed.



Lemma lem_agree_tablecolumns:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (cl: Class) (cols1 cols2 : list Column) (t: Table),
     In (ClassMetamodel_toEObject cl) (allModelElements cm) ->
     In (RelationalMetamodel_toEObject t) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject cl::nil)) ->
     getTableColumns t rm = return cols1 -> 
     getTableColumnsOnLinks t (applyPattern (getRules' Class2Relational cm) (ClassMetamodel_toEObject cl::nil)) = return cols2 ->
     cols1 = cols2
).
intros cm rm tr cl cols1 cols2 t Hinc_cl_cm Hinc_t_apply Htcols_rm Htcols_sp.

(* simpl Hinc_col_apply *)
unfold instantiatePattern, instantiateRuleOnPattern, executeRuleOnPattern in Hinc_t_apply.
simpl in Hinc_t_apply.
try destruct Hinc_t_apply; inversion H.
clear H0. rename H into Hinc_t_apply.
apply rel_invert in Hinc_t_apply.

(* simpl Htcols_sp *)
unfold applyPattern in Htcols_sp.
simpl in Htcols_sp.
unfold applyRuleOnPattern in Htcols_sp.
unfold executeRuleOnPattern in Htcols_sp.
simpl in Htcols_sp.
unfold getAllOuputPatternElementLinks in Htcols_sp.
simpl in Htcols_sp.

destruct (getClassAttributes cl cm) eqn: cl_attrs_ca.
- simpl in Htcols_sp.
  rewrite Hinc_t_apply in Htcols_sp.
  assert (beq_Table t t = true). { apply lem_beq_Table_refl. }
  rewrite H in Htcols_sp.
  inversion Htcols_sp.
  
  (* find sp corresponding to col_t2 *)
  assert (In (RelationalMetamodel_BuildELink TableColumnsReference (BuildTableColumns t cols1)) (allModelLinks rm)).
  { apply (@lem_getTableColumns cm); auto. }
  rewrite tr in H0.
  unfold execute in H0.
  simpl in H0.
  apply concat_map_exists in H0.
  destruct H0.
  destruct H0.
  
  rename x into sp.
  rename H0 into Hinc_sp_cm.
  rename H2 into H3.
  destruct sp.
  - done.
  - destruct sp.
    + destruct c.
      destruct c.
      - (* class impossible *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern,getAllOuputPatternElementLinks in H3.
        simpl in H3.
        destruct (getClassAttributes c0 cm) eqn: c1_ca.
        - simpl in H3.
          destruct H3.
          - {
              apply rel_elink_invert in H0.
              assert (cl = c0). {
              inversion H0.
              rewrite <- Hinc_t_apply in H3.
              inversion H3.
              destruct cl, c0.
              simpl in H5, H6, c1_ca.
              rewrite H5.
              rewrite H6.
              done.
              }
              inversion H0.
              simpl.
              assert (l=l0). {rewrite H2 in cl_attrs_ca. rewrite c1_ca in cl_attrs_ca. inversion cl_attrs_ca. done. }
              rewrite H3.
              done.
            }
          - done.
        - done.
      - (* attribute *)
        unfold applyPhase, applyPattern, matchPhase, matchPattern,applyRuleOnPattern,executeRuleOnPattern in H3.
        simpl in H3.
        destruct (getAttributeDerived c0) eqn: c1_ca.
        - done.
        - simpl in H3.
          rewrite c1_ca in H3. simpl in H3.
          unfold getAllOuputPatternElementLinks in H3.
          simpl in H3.
          destruct (getAttributeType c0 cm) eqn:c1_type_ca.
          - simpl in H3.
            destruct H3.
            - done.
            - done.
          - done.
        
    + done.
- done. 
Qed.

Lemma lem_table_cols_infer_class_attrs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (cl: Class) (attr: Attribute) (t: Table) (col: Column) (cl_attrs: list Attribute) (t_cols: list Column),
     In (ClassMetamodel_toEObject attr) (allModelElements cm) ->
     In (ClassMetamodel_toEObject cl) (allModelElements cm) -> 
     getAttributeDerived attr = false ->
     In (RelationalMetamodel_toEObject col) (allModelElements rm) ->
     In (RelationalMetamodel_toEObject t) (allModelElements rm) -> 
     In (RelationalMetamodel_toEObject col) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject attr::nil)) ->
     In (RelationalMetamodel_toEObject t) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject cl::nil)) ->
     (getClassAttributes cl cm) = Some cl_attrs ->
     (getTableColumns t rm) = Some t_cols ->
     In col t_cols -> 
     In attr cl_attrs
).
Proof.
intros cm rm tr cl attr t col cl_attrs t_cols Hinc_c1_cm Hinc_c2_cm rl_attr_col_guard_ca Hinc_col_rm Hinc_t_rm.
intros Hcol_cos_attr Ht_cos_cl Hcl_attrs Ht_cols Hcol_inc_t_cols.

(* simplify Hcol_cos_attr *)
unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.
rewrite rl_attr_col_guard_ca in Hcol_cos_attr.
simpl in Hcol_cos_attr.


(* simplify Ht_cos_cl *)
unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern in Ht_cos_cl.
simpl in Ht_cos_cl.

destruct Hcol_cos_attr; destruct Ht_cos_cl. 
- {
    rename H into Hcol_cos_attr.
    rename H0 into Ht_cos_cl.
    remember (getTableColumnsOnLinks t 
              (applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject ClassEClass cl]))) as t_cols'.
    remember (applyPattern (getRules' Class2Relational cm) ([ClassMetamodel_BuildEObject ClassEClass cl])) as tm'.

    rename Heqt_cols' into Ht_cols'.
    symmetry in Ht_cols'.

    apply rel_invert in  Ht_cos_cl.
    apply rel_invert in  Hcol_cos_attr.

    (* compute apply_attr_colref: links generated associated with attr *)
    rewrite Heqtm' in Ht_cols'.
    unfold applyPattern in Ht_cols'.
    simpl in Ht_cols'.

    unfold applyRuleOnPattern in Ht_cols'.
    unfold executeRuleOnPattern in Ht_cols'.
    simpl in Ht_cols'.

    unfold getAllOuputPatternElementLinks in Ht_cols'.
    simpl in Ht_cols'.
    remember Ht_cols' as Ht_cols''.
    clear HeqHt_cols''. 
    rewrite Hcl_attrs in Ht_cols'.

    (* Compute tx: table asscoiated with attr *)
    unfold getTableColumnsOnLinks in Ht_cols'.
    simpl in Ht_cols'.
    
    rewrite  Ht_cos_cl in Ht_cols'.
    simpl in Ht_cols'.
    assert (beq_Table t t = true). { apply lem_beq_Table_refl. }
    rewrite H in Ht_cols'.

    assert (Some t_cols = t_cols'). { 
      destruct t_cols' eqn: t_cols'_ca.
       - rename l into t_cols2.
         assert ( t_cols = t_cols2). {
         apply (@lem_agree_tablecolumns cm rm tr cl t_cols t_cols2 t); auto.
                - unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern. 
                  simpl.  left. rewrite Ht_cos_cl. done.
         }
         rewrite H0. done.
      - done.
    }

    rewrite <- H0 in Ht_cols'.
    inversion Ht_cols'.
    
    rewrite <- H2 in Hcol_inc_t_cols.
    rewrite <- Hcol_cos_attr in Hcol_inc_t_cols.
    simpl in Hcol_inc_t_cols.

    clear H2 Ht_cols'.

    clear Hcl_attrs.
    induction cl_attrs.
    - done.
    - simpl in Hcol_inc_t_cols.
      destruct (~~ getAttributeDerived a) eqn:a_guard_ca.
      - simpl.
        simpl in Hcol_inc_t_cols.
        destruct Hcol_inc_t_cols.
        + left. inversion H1. destruct a, attr. simpl in H3, H4. 
          simpl in rl_attr_col_guard_ca, a_guard_ca. apply negbTE  in a_guard_ca. 
          rewrite <- rl_attr_col_guard_ca in a_guard_ca. rewrite H3 H4 a_guard_ca. done. 
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
     In (RelationalMetamodel_toEObject t1) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil)) ->
     In (RelationalMetamodel_toEObject t2) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c2::nil)) ->
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
            apply tr_surj with (t1:=col) in tr'.
            - destruct tr' as [sp_attr]. destruct H as [tp_col]. destruct H as [rl_attr_col].
              destruct H as [Hinc_rl]. destruct H as [Hcol_intp]. destruct H as [Hexec_rl_attr_col]. 
              destruct H as [Hattr_insp]. destruct H as [Hinctp_rm].
              rename H into Hmatch_attr.
              simpl in Hmatch_attr.
              destruct sp_attr eqn:sp_attr_ca; inversion Hmatch_attr. rename c into attr_eo. rename l into sp_attr'.
              destruct sp_attr' eqn:sp_attr'_ca; inversion Hmatch_attr.   
              destruct attr_eo eqn:attr_eo_ca. rename c into attr_Etype. rename c0 into attr.
              destruct attr_Etype eqn:attr_Etype_ca; simpl in attr_Etype; simpl in Hmatch_attr; clear H0 H1.
              *  { (* attr is Class, impossible *) 
                   inversion Hmatch_attr.
                   rewrite <- H0 in Hexec_rl_attr_col.
                   unfold instantiateRuleOnPattern in Hexec_rl_attr_col. simpl in Hexec_rl_attr_col.
                   rewrite <- Hexec_rl_attr_col in Hcol_intp.
                   simpl in Hcol_intp.
                   try destruct Hcol_intp; done.
                 }
              *  { (* attr is Attribute *) 
                 destruct (getAttributeDerived attr) eqn:rl_attr_col_guard_ca.
                     (* getAttributeDerived attr = false *)
                 **  simpl in Hmatch_attr.
                     inversion Hmatch_attr.
                     simpl in Hmatch_attr.
                     inversion Hmatch_attr.
                     rewrite <- H0 in Hexec_rl_attr_col.
                     clear H0.
                     unfold instantiateRuleOnPattern in Hexec_rl_attr_col. 
                     unfold executeRuleOnPattern in Hexec_rl_attr_col. 
                     simpl in Hexec_rl_attr_col. 
                     rewrite rl_attr_col_guard_ca in Hexec_rl_attr_col. 
                     simpl in Hexec_rl_attr_col.
                     rewrite <- Hexec_rl_attr_col in Hcol_intp.
                     simpl in Hcol_intp.
                     destruct Hcol_intp as [Hcol_intp|].
                     simpl in Hcol_intp.
                     exists attr.
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
                            - unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern. 
                              simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. done.
                          }
                      *** { (* getAttributeType attr cm = return c2 *)
                            try apply (@lem_col_table_infer_attr_class cm rm tr attr col c2 t2); auto.
                            - unfold incl in Hattr_insp. apply Hattr_insp. simpl. left. done. 
                            - unfold instantiatePattern,instantiateRuleOnPattern,executeRuleOnPattern. 
                              simpl. rewrite rl_attr_col_guard_ca. simpl. rewrite rl_attr_col_guard_ca. simpl. left. done.
                          }
                 ** (* getAttributeDerived attr = true *)
                    done.
                 } 
            - assumption.
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
     In (RelationalMetamodel_toEObject t1) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil)) ->
     In (RelationalMetamodel_toEObject t2) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c2::nil)) ->
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
    apply tr_surj with (t1:=y) in H.
    - destruct H as [sp]. destruct H as [tp]. destruct H as [r].
      destruct H as [Hinsm]. destruct H as [Hintp]. destruct H as [Hexec]. destruct H as [Hinclsp]. destruct H as [incltp].
      rename H into Hmatch.
      simpl in Hmatch.
      try destruct sp eqn:sp_ca; inversion Hmatch. (* try ... inversion Hmatch; elimin impossible case *)
      try destruct l eqn:l_ca; inversion Hmatch.   (* try ... inversion Hmatch; elimin impossible case *)
      destruct c eqn:c_ca. 
      destruct c0 eqn:c0_ca; simpl in Hmatch; simpl in c3.
      * apply IHHreach_t1_t2 with (c1:=c3) in Hinc_t2_sp2. (* c0 = ClassEClass *)
        ** (* reachable_table_column_step x y -> reachable_class_step cm c1 c3 *)
           assert (reachable_class_step cm c1 c3). 
           {
            try apply (@lem_reach_step cm rm tr x y); auto.
            - unfold incl in Hinclsp. apply Hinclsp. simpl. left. done.
            - inversion Hmatch. rewrite <- H3 in Hexec. 
              unfold instantiateRuleOnPattern in Hexec. simpl in Hexec.
              rewrite <- Hexec in Hintp. done.
           }
           apply reachable_class_trans with c3.
           *** exact. 
           *** exact.
        ** unfold incl in Hinclsp.
           simpl in Hinclsp.
           rewrite <- c_ca in Hinclsp.
           pose (Hinclsp (ClassMetamodel_toEObject c3)) as Hinc.
           apply Hinc.
           left.
           done.
        ** simpl.
           left.
           rewrite <- Hexec in Hintp.
           simpl in Hintp.
           inversion Hmatch.
           rewrite <- H3 in Hintp.
           simpl in Hintp.
           destruct Hintp.
           *** done.
           *** done.
      *  simpl in H1, H2, Hmatch.    (* c0 = AttributeEClass, impoosible *)
         try destruct (getAttributeDerived c3) eqn:derived_ca; inversion Hmatch.
         rewrite <- H3 in Hexec.
         unfold instantiateRuleOnPattern in Hexec. 
         unfold executeRuleOnPattern in Hexec. 
         simpl in Hexec. 
         rewrite derived_ca in Hexec.
         simpl in Hexec.
         rewrite <- Hexec in Hintp.
         simpl in Hintp.
         destruct Hintp; done.
    - unfold reachable_table_step in H0.
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
induction l.
- done.
- destruct (ClassMetamodel_instanceOfEClass ClassEClass a) eqn: ca.
  - destruct a.
    destruct c0.
    - simpl in res.
      inversion res.
      simpl. left.
      done.
    - done.
  - simpl.
    right.
    apply IHl.
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
         (forall (t: RelationalMetamodel_EObject) (r : Rule ClassMetamodel RelationalMetamodel),
           In r (getRules Class2Relational cm) ->
           In t (allModelElements rm) ->
           In t (instantiateRuleOnPattern r (ClassMetamodel_toEObject c1::nil)) ->
           matchPattern (getRules Class2Relational cm) (ClassMetamodel_toEObject c1::nil) = Some r ->
           (t1 <= [[TableClass]] t  | 
             SUCC (forall (t2 : Table), In (RelationalMetamodel_toEObject t2) (allModelElements rm) -> ReachableTable rm t1 t2 ->
                    ~ (beq_string (getTableName t2) "Bad"))                                                                                                  (* post *)
             FAIL Trivial)
         )
         
     | None => Trivial
    end.  
Proof.
  intros cm rm tr .
  destruct (ClassModel_fistClass cm) eqn: first_Class_ca.
  - intros Hgood_class Hreach_class t rl Hinc_rl Hinc_t Hinc_t_rl Hmatch.
    destruct (toModelClass TableClass t) as [t1|] eqn: cast_ca.
     - intros t2 Hinc_t2 Hreach_t_t2.
       simpl in t1.
       (* important here *)
       induction Hreach_t_t2.
       - (* reachable_table_refl *)
         inversion Hmatch.
         rewrite <- H0 in Hinc_t_rl.
         simpl in Hinc_t_rl.
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
           apply tr_surj with (t1:=z) in tr'.  
          + destruct tr' as [sp_z]. destruct H0 as [tp_z]. destruct H0 as [rL_z].
            destruct H0 as [Hinsm_z]. destruct H0 as [Hintp_z]. destruct H0 as [Hexec_z]. 
            destruct H0 as [Hinclsp_z]. destruct H0 as [incltp_z].
            rename H0 into Hmatch_z.
            simpl in Hmatch_z.
            try destruct sp_z eqn:sp_ca; inversion Hmatch_z. 
            try destruct l eqn:l_z_ca; inversion Hmatch_z. 
            destruct c0 as [c0_z] eqn:c0_z_ca; simpl in Hmatch_z.
            destruct c0_z eqn:z_ca; simpl in Hmatch_z.
            (* if c is Class, Important *)
            *  inversion Hmatch_z.
               rewrite <- H3 in Hexec_z.
               rewrite <- Hexec_z in Hintp_z.
               simpl in Hintp_z.
               destruct Hintp_z; auto.
               ** assert (In c0 ([ClassMetamodel_BuildEObject ClassEClass c1])). {
                     simpl. left. symmetry. assumption.
                  }
                  apply Hinclsp_z in H4.
                  rewrite c0_z_ca in H4.
                  apply Hreach_class in H4.
                  - simpl in H.
                    apply rel_invert in H0.
                    rewrite <- H0.
                    done.
                  - clear H1 H2 Hmatch_z.
                    try apply (@lem_reach cm rm tr x z c c1); auto.
                    -  apply (lemma_ClassModel_fistClass_inc); done.
                    - { inversion Hmatch. rewrite <- H2 in Hinc_t_rl. 
                        unfold instantiateRuleOnPattern in Hinc_t_rl. simpl in Hinc_t_rl.
                        destruct (Hinc_t_rl) eqn: Hinc_t_rl_ca.
                        - { simpl. left. simpl in cast_ca.
                            rewrite <- e in cast_ca. simpl in cast_ca.
                            inversion cast_ca. done. }
                        - done.
                      }
                    - { simpl. left. done. }
                    - apply (@reachable_table_trans rm x y z H Hreach_t_t2).
             (* if c is Attribute, Trivial *)
             * simpl in H1, H2, Hmatch_z.
               try destruct (getAttributeDerived c1) eqn:derived_ca; inversion Hmatch_z.
               rewrite <- H3 in Hexec_z.
               unfold instantiateRuleOnPattern in Hexec_z. 
               unfold executeRuleOnPattern in Hexec_z. 
               simpl in Hexec_z. 
               rewrite derived_ca in Hexec_z.
               simpl in Hexec_z.
               rewrite <- Hexec_z in Hintp_z.
               simpl in Hintp_z.
               destruct Hintp_z; done.
           + done.
     - done.
  - done.
Qed.



(* Lemma lem_disagree_colrefs:
 (forall (cm : ClassModel) (rm : RelationalModel), rm = execute Class2Relational cm -> (* transformation *)
   forall (attr:Attribute) (t1 : Table) (col: Column) (tls: list RelationalMetamodel_ELink),
     In (RelationalMetamodel_toEObject col) (instantiatePattern (getRules Class2Relational cm) (ClassMetamodel_toEObject attr::nil)) ->
     getColumnReference col rm = return t1 ->
     getAttributeType attr cm = None ->
     False
).
Proof.
Admitted. *)
