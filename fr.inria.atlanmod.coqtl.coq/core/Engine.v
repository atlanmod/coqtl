Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.

Set Implicit Arguments.

Class TransformationEngineTypeClass (TransformationDef: Type) (RuleDef: Type) (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    allSourceModelElements: SourceModel -> list SourceModelElement;
    allTargetModelElements: TargetModel -> list TargetModelElement;
    
    getRulesFun: TransformationDef -> list RuleDef;

    executeFun: TransformationDef -> SourceModel -> TargetModel;
    matchPatternFun: TransformationDef -> list SourceModelElement -> SourceModel -> option RuleDef;  
    instantiateRuleOnPatternFun: RuleDef -> list SourceModelElement -> SourceModel -> list TargetModelElement; 

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

    outp_incl :
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef),
          tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
          incl (instantiateRuleOnPatternFun r sp sm) (allTargetModelElements tm);
          (* /\  incl (applyRuleOnPatternFun r sp sm) (allTargetModeLinks tm)) *) 

    match_incl :
        forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleDef),
          matchPatternFun tr sp sm = Some r -> In r (getRulesFun tr);

    match_fun :
        forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
          matchPatternFun tr sp sm = Some r1 -> matchPatternFun tr sp sm = Some r2 -> r1 = r2;
    
    (*     
    tr_surj'' : 
    forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
      tm = executeFun tr sm -> In t1 (allTargetModelLinks tm) ->
      (exists (sp : list SourceModelElement) (tpl : list TargetModelLink) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tpl /\
        applyRuleOnPatternFun r sp sm = tpl /\
        incl sp (allSourceModelElements sm) /\
        incl tpl (allTargetModelLinks tm) /\
        matchPatternFun tr sp sm = Some r ); *)
                                            
  }.