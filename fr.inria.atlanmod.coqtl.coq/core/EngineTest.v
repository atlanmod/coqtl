(** * Examplified transformation engine 

    In this section, we experiment a simplified type 
    classes for metamodel, model and transformation engine.
    The goal is to better understand relationship among them.
    
    Note: Not intended to be used. *)

Require Import Omega.
Require Import List.      (* sequence *)
Require Import String.
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)


Set Implicit Arguments.

(** ** Metamodel type class *)

Class Metamodel (ModelElement: Type) (ModelLink: Type)  :=
  {
    ModelClass: Type;
    ModelReference: Type;
    
    (* Denotation *)
    denoteModelClass: ModelClass -> Set;
    denoteModelReference: ModelReference -> Set;

    (* Downcasting *)
    toModelClass: forall (t:ModelClass), ModelElement -> option (denoteModelClass t);
    toModelReference: forall (t:ModelReference), ModelLink -> option (denoteModelReference t);

    (* Default object of that class *)
    bottomModelClass: forall (c:ModelClass), (denoteModelClass c);

    (* Upcasting *)
    toModelElement: forall (t: ModelClass), (denoteModelClass t) -> ModelElement;

    (* Decidability of equality *)
    eqModelClass_dec: forall (c1:ModelClass) (c2:ModelClass), { c1 = c2 } + { c1 <> c2 };
    eqModelReference_dec: forall (c1:ModelReference) (c2:ModelReference), { c1 = c2 } + { c1 <> c2 };

    (* Constructors *)
    BuildModelElement: forall (r: ModelClass), (denoteModelClass r) -> ModelElement;
    BuildModelLink:  forall (r: ModelReference), (denoteModelReference r) -> ModelLink;
  }.


(** ** Model type class *)
Class Model (ModelElement : Type) (ModelLink : Type) (MM: Metamodel ModelElement ModelLink):= 
{
  allModelElements : list ModelElement;
  allModelLinks : list ModelLink;
}.

(** ** Transformation engine type class *)
Class TransformationEngineTypeClass :=
  {
    (* Source Types *)
    SourceModelElement: Type; 
    SourceModelLink: Type;
    
    (* Target Types *)
    TargetModelElement: Type;
    TargetModelLink: Type;
    
    (* Metamodel Types *)
    ofMMS: Metamodel SourceModelElement SourceModelLink;
    ofMMT: Metamodel TargetModelElement TargetModelLink;
    
    (* Transformation Types *)
    TransformationDef: Type;
    RuleDef: Type;
    
    (* Functions *)
    getRulesFun: TransformationDef -> list RuleDef;
    executeFun: TransformationDef -> Model ofMMS -> Model ofMMT;
    matchPatternFun: TransformationDef -> list SourceModelElement -> Model ofMMS -> option RuleDef;  
    instantiateRuleOnPatternFun: RuleDef -> list SourceModelElement -> Model ofMMS -> list TargetModelElement; 
    
    (* Theorems *) 
    tr_surj' : 
    forall (tr: TransformationDef) (sm : Model ofMMS) (tm: Model ofMMT) (t1 : TargetModelElement),
      tm = executeFun tr sm -> In t1 (@allModelElements _ _ _ tm) ->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
        In r (getRulesFun tr) /\
        In t1 tp /\
        instantiateRuleOnPatternFun r sp sm = tp /\
        incl sp (@allModelElements _ _ _ sm) /\ (* OR shortly (incl sp allModelElements) *)
        incl tp (@allModelElements _ _ _ tm) /\
        matchPatternFun tr sp sm = Some r );

    outp_incl :
        forall (tr: TransformationDef) (sm : Model ofMMS) (tm: Model ofMMT) (sp : list SourceModelElement) (r: RuleDef),
          tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (@allModelElements _ _ _ sm) ->
          incl (instantiateRuleOnPatternFun r sp sm) (@allModelElements _ _ _ tm);
          (* /\  incl (applyRuleOnPatternFun r sp sm) (allTargetModeLinks tm)) *) 

    match_incl :
        forall (tr: TransformationDef) (sm : Model ofMMS) (sp : list SourceModelElement) (r: RuleDef),
          matchPatternFun tr sp sm = Some r -> In r (getRulesFun tr);

    match_fun :
        forall (tr: TransformationDef) (sm : Model ofMMS) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
          matchPatternFun tr sp sm = Some r1 -> matchPatternFun tr sp sm = Some r2 -> r1 = r2;

  }.
