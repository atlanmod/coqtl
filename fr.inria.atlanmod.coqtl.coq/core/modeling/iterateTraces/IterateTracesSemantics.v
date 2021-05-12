Require Import String.

Require Import core.utils.Utils.
Require Import core.modeling.Metamodel.
Require Import core.Model.
Require Import core.Syntax.
Require Import Bool.
Require Import Arith.
Require Import Semantics.
Require Import core.EqDec.
Scheme Equality for list.
 

Section IterateTracesSemantics.

  Context {SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type}.
  Context {smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference}.
  Context {eqdec_sme: EqDec SourceModelElement}. (* need decidable equality on source model elements *)
  Context {TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type}.
  Context {tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference}.
  Context (SourceModel := Model SourceModelElement SourceModelLink).
  Context (TargetModel := Model TargetModelElement TargetModelLink).
  Context (Transformation := @Transformation SourceModelElement SourceModelLink TargetModelElement TargetModelLink).

  (** * Apply **)

  Definition applyReferenceOnPatternTraces
             (oper: OutputPatternElementReference)
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
      | Some l => optionToList (applyReferenceOnPatternTraces oper tr sm sp iter l tls)
      | None => nil
      end) (OutputPatternElement_getOutputElementReferences ope).

  Definition applyIterationOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun o => applyElementOnPatternTraces o tr sm sp iter tls)
      (Rule_getOutputPatternElements r).

  Definition applyRuleOnPatternTraces (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun i => applyIterationOnPatternTraces r tr sm sp i tls)
      (indexes (evalIteratorExpr r sm sp)).

  Definition applyPatternTraces (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tls: list TraceLink): list TargetModelLink :=
    flat_map (fun r => applyRuleOnPatternTraces r tr sm sp tls) (matchPattern tr sm sp).

  (** * Execute **)

  Fixpoint noDup_sp (l : list (list SourceModelElement)) : list (list SourceModelElement) :=
    match l with
      | x::xs => if (list_beq SourceModelElement core.EqDec.eq_b x (hd nil xs)) then noDup_sp xs else x::(noDup_sp xs)
      | nil => nil
    end.
  
  Lemma In_noDup_sp: forall (l: list (list SourceModelElement)) (sp: list SourceModelElement),
    In sp (noDup_sp l) -> In sp l.
  Proof.
    intros.
    induction l.
    - simpl in H. contradiction.
    - simpl. simpl in H.
      destruct (list_beq SourceModelElement core.EqDec.eq_b a (hd nil l)).
      * right. auto.
      * simpl in H.
        destruct H.
        + auto.
        + auto.       
  Qed.       

  Definition instantiateTraces (tr: Transformation) (sm : SourceModel) :=
    let tls := trace tr sm in
      ( map (TraceLink_getTargetElement) tls, tls ).
  
  Definition applyTraces (tr: Transformation) (sm : SourceModel) (tls: list (@TraceLink SourceModelElement TargetModelElement)): list TargetModelLink :=
    flat_map (fun sp => applyPatternTraces tr sm sp tls) (noDup_sp (map (TraceLink_getSourcePattern) tls)).
  
  Definition executeTraces (tr: Transformation) (sm : SourceModel) : TargetModel :=
    let (elements, tls) := instantiateTraces tr sm in
    let links := applyTraces tr sm tls in
    Build_Model elements links.

End IterateTracesSemantics.
