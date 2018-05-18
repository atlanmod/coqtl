Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.

Set Implicit Arguments.

Class TransformationEngineTypeClass (TransformationDef: Type) (RuleDef: Type) (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    executeFun: TransformationDef -> SourceModel -> TargetModel;
    getRulesFun: TransformationDef -> list RuleDef;
    instantiateRuleOnPatternFun: RuleDef -> list SourceModelElement -> SourceModel -> list TargetModelElement; 
    matchPatternFun: TransformationDef -> list SourceModelElement -> SourceModel -> option RuleDef;  
    allSourceModelElements: SourceModel -> list SourceModelElement;
    allTargetModelElements: TargetModel -> list TargetModelElement;

    tr_surj' : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = executeFun tr sm -> In t1 (allTargetModelElements tm) ->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tp /\
        instantiateRuleOnPatternFun r sp sm = tp /\
        incl sp (allSourceModelElements sm) /\
        incl tp (allTargetModelElements tm) /\
        matchPatternFun tr sp sm = Some r );

    thrm :
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef),
          tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
          incl (instantiateRuleOnPatternFun r sp sm) (allTargetModelElements tm);

    thrm1 :
        forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleDef),
          matchPatternFun tr sp sm = Some r -> In r (getRulesFun tr);
                                            
  }.