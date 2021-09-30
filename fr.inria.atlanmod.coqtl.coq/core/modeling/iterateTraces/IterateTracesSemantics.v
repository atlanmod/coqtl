Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import core.EqDec.
Require Import core.TransformationConfiguration.
Require Import core.modeling.ModelingTransformationConfiguration.
Scheme Equality for list.
 

Section IterateTracesSemantics.

Context {tc: TransformationConfiguration} {mtc: ModelingTransformationConfiguration tc}. 

(** * Apply **)

Definition applyLinkOnPatternTraces
            (oper: OutputPatternLink)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink): option TargetModelLink :=
  evalOutputPatternLinkExpr sm sp te iter tls oper.

Definition applyElementOnPatternTraces
            (ope: OutputPatternElement)
            (tr: Transformation)
            (sm: SourceModel)
            (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun oper => 
    match (evalOutputPatternElementExpr sm sp iter ope) with 
    | Some l => optionToList (applyLinkOnPatternTraces oper tr sm sp iter l tls)
    | None => nil
    end) (OutputPatternElement_getOutputLinks ope).

Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun o => applyElementOnPatternTraces o tr sm sp iter tls)
    (Rule_getOutputPatternElements r).

Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
    (seq 0 (evalIteratorExpr r sm sp)).

Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

(** * Execute **)

Fixpoint noDup_sp (l : list (list SourceModelElement)) : list (list SourceModelElement) :=
  match l with
    | x::xs => 
      match xs with
        | x2::x2s => if (list_beq SourceModelElement core.EqDec.eq_b x x2) then noDup_sp xs else x::(noDup_sp xs)
        | nil => x::nil
      end
    | nil => nil
  end.

Lemma In_noDup_sp_cons: forall (l: list (list SourceModelElement)) (sp x: list SourceModelElement),
  In sp (noDup_sp l) -> In sp (noDup_sp (x::l)).
Proof.
  intros.
  simpl.  
  destruct l eqn:dstl.
  - contradiction.
  - destruct (list_beq SourceModelElement eq_b x l0) eqn:dsteq.
    + assumption.
    + simpl.
      simpl in H.
      right.
      assumption.
Qed.

Lemma In_noDup_sp_cons': forall (l: list (list SourceModelElement)) (sp x: list SourceModelElement),
  In sp (noDup_sp (x::l)) -> sp = x \/ In sp (noDup_sp l).
Proof.
  intros.
  simpl in H.
  destruct l eqn:dstl.
  - simpl in H. crush.
  - destruct (list_beq SourceModelElement eq_b x l0) eqn:dsteq.
    + right. assumption.
    + simpl in H.
      destruct H.
      * auto.
      * right. auto.
Qed.

Lemma In_noDup_sp: forall (l: list (list SourceModelElement)) (sp: list SourceModelElement),
  In sp (noDup_sp l) <-> In sp l.
Proof.
  split.
  --  intros.
      induction l.
      - simpl in H. contradiction.
      - simpl. simpl in H.
        destruct l eqn:dstl.
        + simpl in H. auto.
        + destruct (list_beq SourceModelElement core.EqDec.eq_b a l0) eqn:dsteq.
          * right. apply IHl. assumption.
          * simpl in H.
            destruct H.
            ++ auto.
            ++ auto. 
  -- intros.
      induction l.
      - contradiction.
      - simpl in H.
        destruct l eqn:dstl.
        * auto.
        * simpl.
          destruct (list_beq SourceModelElement core.EqDec.eq_b a l0) eqn:dsteq.
          + destruct l1 eqn:dstl1.
            ++ destruct H.
              ** rewrite <- H. unfold In. left. 
                Admitted.
                (* here it shows the problem for an explicit eq_b*)

Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
  let tls := trace tr sm in
    ( map (TraceLink_getTargetElement) tls, tls ).

Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list TraceLink): list TargetModelLink :=
  flat_map (fun sp => applyPatternTraces tr sm sp tls) (noDup_sp (map (TraceLink_getSourcePattern) tls)).

Definition executeTraces (tr: Transformation) (sm : SourceModel) : TargetModel :=
  let (elements, tls) := instantiateTraces tr sm in
  let links := applyTraces tr sm tls in
  Build_Model elements links.

End IterateTracesSemantics.
