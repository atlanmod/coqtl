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
    getModelElementsInModelLink : TargetModel -> TargetModelLink -> list TargetModelElement;
    
    tr_correctness : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) 
               (sp : list SourceModelElement) (r: RuleDef) (tl: TargetModelLink) (tpl : list TargetModelLink),
          tm = executeFun tr sm -> 
          In r (getRulesFun tr) -> 
          incl sp (allSourceModelElements sm) ->
          applyPatternFun tr sm sp = Some tpl ->
          incl tpl (allTargetModelLinks tm) ->
          In tl tpl -> 
          incl (getModelElementsInModelLink tm tl) (allTargetModelElements tm)
    ;

    (* Convergence: apply rules in different order get same output, our CoqTL does not hold on this *)
    tr_converge : 
    forall (tr1: TransformationDef) (tr2: TransformationDef) (sm : SourceModel) (tm1: TargetModel) (tm2: TargetModel),
          incl (getRulesFun tr1) (getRulesFun tr2) ->
          incl (getRulesFun tr2) (getRulesFun tr1) ->
          tm1 = executeFun tr1 sm -> 
          tm2 = executeFun tr2 sm -> 
          tm1 = tm2
    ;
    
    (* Additivity *)
    (*  remove binding, the links is a subset of tm created before *)
    tr_additivity : 
    forall (tr1: TransformationDef) (tr2: TransformationDef) (sm : SourceModel) (tm1: TargetModel) (tm2: TargetModel) 
    (r1: RuleDef) (r2: RuleDef) (rs: list RuleDef) (sp : list SourceModelElement) (tp : list TargetModelElement) 
    (tpl1 : list TargetModelLink) (tpl2 : list TargetModelLink),
          (getRulesFun tr1) = r1 :: rs ->
          (getRulesFun tr2) = r2 :: rs ->
          tm1 = executeFun tr1 sm ->
          tm2 = executeFun tr2 sm ->
          instantiateRuleOnPatternFun r1 tr1 sm sp = Some tp ->
          instantiateRuleOnPatternFun r2 tr2 sm sp = Some tp ->
          applyRuleOnPatternFun r1 tr1 sm sp tp = Some tpl1 ->
          applyRuleOnPatternFun r2 tr2 sm sp tp = Some tpl2 ->
          incl tpl1 tpl2 ->
          incl (allTargetModelElements tm1) (allTargetModelElements tm2) 
    ;
    

    (* Well-formedness *)
    

  }.
