Require Import String.
        
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Model.

Set Implicit Arguments.


(*TODO Type class inheirentence *)
Class TransformationEngineTypeClass 
  (TransformationDef: Type) (RuleDef: Type) 
  (OutputPatternElementDef: Type) (OutputPatternElementReferenceDef: Type) 
  (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) 
  (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    allSourceModelElements: SourceModel -> list SourceModelElement;
    allSourceModelLinks: SourceModel -> list SourceModelLink;
    allTargetModelElements: TargetModel -> list TargetModelElement;
    allTargetModelLinks: TargetModel -> list TargetModelLink;

    getRulesFun: TransformationDef -> list RuleDef;
    getOutputPatternElementsFun: RuleDef -> list OutputPatternElementDef;
    getOutputPatternElementReferencesFun: OutputPatternElementDef -> list OutputPatternElementReferenceDef;

    executeFun: TransformationDef -> SourceModel -> TargetModel;
    
    matchPatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option RuleDef;
    instantiatePatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);
    applyPatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);

    matchRuleOnPatternFun:  RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> option bool;
    instantiateRuleOnPatternFun: RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
    applyRuleOnPatternFun: RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> list TargetModelElement -> option (list TargetModelLink);

    (* Correctness (the transformation does not generate dangling links)  our CoqTL does not hold on this *)
    tr_correctness : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
      tm = executeFun tr sm -> In t1 (allTargetModelLinks tm) ->
      (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tpl /\
        applyRuleOnPatternFun r tr sm sp tel = Some tpl /\
        incl sp (allSourceModelElements sm) /\
        incl tpl (allTargetModelLinks tm) /\
        matchPatternFun tr sm sp = Some r );

    (* Convergence our CoqTL does not hold on this *)

    (* Additivity *)
    (*  remove binding, the links is a subset of tm created before *)
    
    (* Well-formedness *)
    

  }.
