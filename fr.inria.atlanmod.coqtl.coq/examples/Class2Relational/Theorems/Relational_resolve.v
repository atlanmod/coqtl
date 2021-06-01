Require Import String.
Require Import Coq.Logic.Eqdep_dec.
Require Import Arith.
Require Import Coq.Arith.Gt.
Require Import Coq.Arith.EqNat.
Require Import List.
Require Import Omega.

Require Import core.utils.Utils.
Require Import core.Semantics.
Require Import core.Certification.
Require Import core.modeling.Metamodel.
Require Import core.Model.

Require Import examples.Class2Relational.Class2Relational.
Require Import examples.Class2Relational.ClassMetamodel.
Require Import examples.Class2Relational.RelationalMetamodel.


Theorem Relational_Column_Reference_definedness:
forall (cm : ClassModel) (rm : RelationalModel), 
  (* transformation *) rm = execute Class2Relational cm ->
  (* precondition *)  (forall (att : Attribute),
    In (ClassMetamodel_toObject AttributeClass att) (allModelElements cm) ->
        getAttributeType att cm <> None) ->
  (* postcondition *)  (forall (col: Column),
    In (RelationalMetamodel_toObject ColumnClass col) (allModelElements rm) ->
      getColumnReference col rm <> None). 
Proof.
    intros cm rm tr pre.
    intros. 
    rewrite tr in H.
    apply tr_execute_in_elements in H.
    do 2 destruct H. 
    destruct x eqn: sp_ca. (* Case analysis on source pattern *)
    - (* Empty pattern *) contradiction H0.
    - destruct l eqn: l_ca.
      + (* Singleton *) 
        apply allTuples_incl in H.
        unfold incl in H.
        specialize (H c).
        assert (In c [c]). { left. reflexivity. }
        specialize (H H1).  
        rename x into sp.
        do 2 destruct c. (* Case analysis on source element type *)
        * (* [Class] *) simpl in H0.
          destruct H0.
          ** admit. (* contradiction in H0 *)
          ** crush.
        * (* [Attribute] *) destruct c0 eqn: attr_ca.
          destruct b eqn: d_ca.
          -- (* derived *) contradiction H0.
          -- (* not derived *) simpl in H0.
              destruct H0. 
              ++ remember (applyPattern Class2Relational cm 
              [ClassMetamodel_BuildObject AttributeClass
             (BuildAttribute n false s)]).
             unfold applyPattern in Heql0.
             unfold applyRuleOnPattern in Heql0.
             unfold applyIterationOnPattern in Heql0.
             unfold applyElementOnPattern in Heql0.
             simpl in Heql0.
             unfold ConcreteExpressions.makeLink in Heql0.
             unfold ConcreteExpressions.wrapOptionLink in Heql0.
              
                 admit. (* todo *)
              ++ contradiction H0.
      + (* Other patterns *) do 2 destruct c.
        * destruct c0. destruct c; contradiction H0.
        * destruct c0. destruct c; contradiction H0.
Admitted.
