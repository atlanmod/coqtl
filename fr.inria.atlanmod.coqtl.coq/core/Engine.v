(** * Transformation Engine Type Class 

    In this section, we introduce a type class for transformation engine.

    We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

    An example instaniated transformation engine is CoqTL. *)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.TopUtils.
Require Import core.Model.

Set Implicit Arguments.

(* OutputPatternElement and OutputPatternElementReference removed because of type parameters *)
Class TransformationEngine :=
  {
    SourceModelElement: Type;
    SourceModelClass: Type;
    SourceModelLink: Type;
    SourceModelReference: Type;
    TargetModelElement: Type;
    TargetModelClass: Type;
    TargetModelLink: Type;
    TargetModelReference: Type;

    SourceModel := Model SourceModelElement SourceModelLink;
    TargetModel := Model TargetModelElement TargetModelLink;
    
    Transformation: Type;
    Rule: Type;
    OutputPatternElement: list SourceModelClass -> Type -> Type;
    OutputPatternElementReference: list SourceModelClass -> Type -> TargetModelClass -> Type;

    (** ** Transformation Engine Accessors *)

    (** *** getRules
        Returns the rules of the given transformation. *)
    getRules: Transformation -> list Rule;

    (** *** getInTypes **)
    getInTypes: Rule -> list SourceModelClass;

    (** *** getIteratorType **)
    getIteratorType: Rule -> Type;

    (** *** getOutputPattern **)
    getOutputPattern: forall x:Rule, list (OutputPatternElement (getInTypes x) (getIteratorType x));

    maxArity (tr: Transformation) : nat :=
    max (map (length (A:=SourceModelClass)) (map getInTypes (getRules tr)));

    (** ** Transformation Engine Functions *)
    
    (** *** execute
        Given a _source model_ and a _transformation_, _execute_ should return a _target model_. *)
    execute: Transformation -> SourceModel -> TargetModel;
    
    (** *** matchPattern *)
    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;

    (** *** matchRuleOnPattern *)
    matchRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option bool;

    (** *** instantiatePattern *)
    instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);

    (** *** instantiateRuleOnPattern *)
    instantiateRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
      
    (** *** applyPattern *)
    applyPattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
      
    (** *** applyRuleOnPattern *)
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
      
    (** ** Theorems of the Transformation Engine *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
        In te (allModelElements (execute tr sm)) <->
        (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
            incl sp (allModelElements sm) /\
            instantiatePattern tr sm sp = Some tp /\
            In te tp);

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (execute tr sm)) <->
        (exists (sp : list SourceModelElement) (tpl : list TargetModelLink),
            incl sp (allModelElements sm) /\
            applyPattern tr sm sp = Some tpl /\
            In tl tpl);

    tr_execute_nil_tr :
      forall (tr: Transformation) (sm : SourceModel),
        getRules tr = nil ->
        allModelElements (execute tr sm) = nil;

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
        instantiatePattern tr sm sp = Some tp ->
        In te tp <->
        (exists (r : Rule) (tp1 : list TargetModelElement),
            In r (matchPattern tr sm sp) /\
            instantiateRuleOnPattern r tr sm sp = Some tp1 /\
            In te tp1);

    tr_instantiatePattern_nil_tr : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        getRules tr = nil ->
        instantiatePattern tr sm sp = None;

    tr_instantiatePattern_maxArity : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        instantiatePattern tr sm sp = None; 

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tpl: list TargetModelLink) (tl : TargetModelLink),
        applyPattern tr sm sp = Some tpl ->
        In tl tpl <->
        (exists (r : Rule) (tpl1 : list TargetModelLink),
            In r (matchPattern tr sm sp) /\
            applyRuleOnPattern r tr sm sp = Some tpl1 /\
            In tl tpl1);

    tr_applyPattern_nil_tr : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        getRules tr = nil ->
        applyPattern tr sm sp = None;

    tr_applyPattern_maxArity : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        applyPattern tr sm sp = None;    

    tr_matchPattern_in :
      forall (tr: Transformation) (sm : SourceModel),
      forall (sp : list SourceModelElement)(r : Rule),
        In r (matchPattern tr sm sp) <->
        In r (getRules tr) /\
        matchRuleOnPattern r tr sm sp = return true;

    tr_matchPattern_nil_tr : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        getRules tr = nil ->
        matchPattern tr sm sp = nil;
    
    tr_matchPattern_maxArity : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        matchPattern tr sm sp = nil;

    tr_matchRuleOnPattern_inTypes : 
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (getInTypes r) ->
        matchRuleOnPattern r tr sm sp = None;
    
  }.

Theorem match_functionality :  
  forall (eng: TransformationEngine)
    (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r1: list Rule) (r2: list Rule),
          matchPattern tr sm sp  = r1 -> matchPattern tr sm sp = r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.

Theorem incl_equiv_to_surj:
  forall (eng: TransformationEngine),
    (forall (tr: Transformation) (sm : SourceModel)
       (sp : list SourceModelElement) (tp: list TargetModelElement) (tp1: list TargetModelElement)
       (r : Rule),
        instantiateRuleOnPattern r tr sm sp = Some tp1 ->
        In r (matchPattern tr sm sp) ->
        instantiatePattern tr sm sp = Some tp ->
        incl tp1 tp) <->
    (forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
        instantiatePattern tr sm sp = Some tp ->
        (exists (r : Rule) (tp1 : list TargetModelElement),
            In r (matchPattern tr sm sp) /\
            instantiateRuleOnPattern r tr sm sp = Some tp1 /\
            In te tp1) ->
        In te tp).
Proof.
  split.
  - intros.
    destruct H1. destruct H1. destruct H1. destruct H2.
    + pose (H tr sm sp tp x0 x H2 H1 H0).
      apply i in H3.
      assumption.
  - intros.
    unfold incl.
    intros.
    pose (H tr sm sp tp a H2).
    apply i.
    exists r, tp1.
    split. assumption.
    split. assumption.
    assumption.
Qed.

