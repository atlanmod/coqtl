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
Require Import core.Expressions.

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

    (** ** Accessors *)
    
    getRules: Transformation -> list Rule;
    getInTypes: Rule -> list SourceModelClass;
    getIteratorType: Rule -> Type;
    getOutputPattern: forall x:Rule, list (OutputPatternElement (getInTypes x) (getIteratorType x));
    getOutType (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) : TargetModelClass;
    getOutputElementReferences: forall (InElTypes:list SourceModelClass) (IterType: Type) (o:OutputPatternElement InElTypes IterType),
        list (OutputPatternElementReference InElTypes IterType (getOutType o));

    maxArity (tr: Transformation) : nat :=
      max (map (length (A:=SourceModelClass)) (map getInTypes (getRules tr)));

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;
    matchRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);
    instantiateRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelElement);
    instantiateElementOnPattern: forall r:Rule, OutputPatternElement (getInTypes r) (getIteratorType r) -> SourceModel -> list SourceModelElement -> nat -> option TargetModelElement;
    
    applyPattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelLink);
    applyElementOnPattern: forall r:Rule, OutputPatternElement (getInTypes r) (getIteratorType r) -> Transformation -> SourceModel -> list SourceModelElement -> nat -> option (list TargetModelLink);
    applyReferenceOnPattern:
      forall (r: Rule)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        Transformation -> SourceModel -> list SourceModelElement -> nat -> option TargetModelLink;
    
    evalIterator: forall r:Rule, SourceModel -> list SourceModelElement -> list (getIteratorType r); 
    
    (** ** Theorems *)

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
        (instantiatePattern tr sm sp = Some tp /\
         In te tp) <->
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

    tr_instantiateRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
        (instantiateRuleOnPattern r tr sm sp = Some tp /\
         In te tp) <->
        (exists (i: nat) (tp1: list TargetModelElement),
            i < length (evalIterator r sm sp) /\
            instantiateIterationOnPattern r sm sp i = Some tp1 /\
            In te tp1);
    
    tr_instantiateRuleOnPattern_inTypes : 
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (getInTypes r) ->
        instantiateRuleOnPattern r tr sm sp = None;

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement) (i:nat),
        (instantiateIterationOnPattern r sm sp i = Some tp /\
         In te tp) <->
        (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
            In ope (getOutputPattern r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);
    
    tr_instantiateIterationOnPattern_inTypes : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        instantiateIterationOnPattern r sm sp i = None;

    tr_instantiateIterationOnPattern_iterator : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        i >= length (evalIterator r sm sp) ->
        instantiateIterationOnPattern r sm sp i = None;

    tr_instantiateElementOnPattern_inTypes : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        length sp <> length (getInTypes r) ->
        instantiateElementOnPattern ope sm sp i = None;

    tr_instantiateElementOnPattern_iterator : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        i >= length (evalIterator r sm sp) ->
        instantiateElementOnPattern ope sm sp i = None;
    
    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tpl: list TargetModelLink) (tl : TargetModelLink),
        (applyPattern tr sm sp = Some tpl /\
         In tl tpl) <->
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

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tpl: list TargetModelLink) (tl : TargetModelLink),
        (applyRuleOnPattern r tr sm sp = Some tpl /\
         In tl tpl) <->
        (exists (i: nat) (tpl1: list TargetModelLink),
            i < length (evalIterator r sm sp) /\
            applyIterationOnPattern r tr sm sp i = Some tpl1 /\
            In tl tpl1);
    
    tr_applyRuleOnPattern_inTypes : 
      forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
        length sp <> length (getInTypes r) ->
        applyRuleOnPattern r tr sm sp = None;

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tpl: list TargetModelLink) (tl : TargetModelLink) (i:nat),
        (applyIterationOnPattern r tr sm sp i = Some tpl /\
         In tl tpl) <->
        (exists (ope: OutputPatternElement (getInTypes r) (getIteratorType r)) (tpl1: list TargetModelLink),
            In ope (getOutputPattern r) /\ 
            applyElementOnPattern ope tr sm sp i = Some tpl1 /\
            In tl tpl1);
    
    tr_applyIterationOnPattern_inTypes : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        length sp <> length (getInTypes r) ->
        applyIterationOnPattern r tr sm sp i = None;

    tr_applyIterationOnPattern_iterator : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
        i >= length (evalIterator r sm sp) ->
        applyIterationOnPattern r tr sm sp i = None;

    tr_applyElementOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tpl: list TargetModelLink) (tl : TargetModelLink) (i:nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        (applyElementOnPattern ope tr sm sp i = Some tpl /\
         In tl tpl) <->
        (exists (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
            In ope (getOutputPattern r) /\ 
            applyReferenceOnPattern oper tr sm sp i = Some tl);

    tr_applyElementOnPattern_inTypes : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        length sp <> length (getInTypes r) ->
        applyElementOnPattern ope tr sm sp i = None;

    tr_applyElementOnPattern_iterator : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (getInTypes r) (getIteratorType r)),
        i >= length (evalIterator r sm sp) ->
        applyElementOnPattern ope tr sm sp i = None;

    tr_applyReferenceOnPattern_inTypes : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        length sp <> length (getInTypes r) ->
        applyReferenceOnPattern oper tr sm sp i = None;

    tr_applyReferenceOnPattern_iterator : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (getInTypes r) (getIteratorType r) (getOutType ope)),
        i >= length (evalIterator r sm sp) ->
        applyReferenceOnPattern oper tr sm sp i = None;
    
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
