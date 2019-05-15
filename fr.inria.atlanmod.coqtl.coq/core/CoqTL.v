Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.
Require Import core.Engine.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.

  (** * Abstract Syntax **)

  (** ** Expression Types **)
  
  Definition outputReferenceTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass)  (tref: TargetModelReference):=
    denoteFuncOfClasses smm (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).
  
  Definition outputPatternElementTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFuncOfClasses smm (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
             (sclasses : list SourceModelClass) (itype: Type) :=
    denoteFuncOfClasses smm (sclasses) (list itype).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFuncOfClasses smm (sclasses) bool.

  (** ** Syntax Types **)
  
  Inductive MatchedOutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type := 
    BuildMatchedOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       MatchedOutputPatternElement InElTypes IterType.
  
  Inductive MatchedRule : Type := 
    BuildMatchedRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
        (SourceModel -> (iteratedListTypes InElTypes IterType))
        -> list (MatchedOutputPatternElement InElTypes IterType)
        -> MatchedRule.
  
  Inductive MatchedTransformation : Type := 
    BuildMatchedTransformation :
      list MatchedRule ->
      MatchedTransformation.
  
  Inductive OutputPatternElementReference (InElTypes: list SourceModelClass) (IterType: Type) (OutType:TargetModelClass): Type :=
    BuildOutputPatternElementReference :
      forall (OutRef: TargetModelReference),
        (MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType OutRef)) ->
        OutputPatternElementReference InElTypes IterType OutType.

  Inductive OutputPatternElement (InElTypes: list SourceModelClass) (IterType: Type) : Type := 
    BuildOutputPatternElement :
      string ->
      forall (OutType:TargetModelClass),
       (IterType -> SourceModel -> (outputPatternElementTypes InElTypes OutType)) ->
       list (OutputPatternElementReference InElTypes IterType OutType)-> OutputPatternElement InElTypes IterType.
  
  Inductive Rule : Type := 
    BuildRule :
      string ->
      forall (InElTypes: list SourceModelClass),
        (SourceModel -> (guardTypes InElTypes))
        -> forall (IterType: Type),
        (SourceModel -> (iteratedListTypes InElTypes IterType))
        -> list (OutputPatternElement InElTypes IterType)
        -> Rule.
  
  Inductive Transformation : Type := 
    BuildTransformation :
      list Rule ->
      Transformation.

  (** ** Accessors **)

  Definition OutputPatternElementReference_getRefType {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) : TargetModelReference :=
    match o with 
      BuildOutputPatternElementReference _ _ _ y _ => y
    end.

  Definition OutputPatternElementReference_getOutputReference {InElTypes: list SourceModelClass} {IterType: Type} {OutType:TargetModelClass} (o: OutputPatternElementReference InElTypes IterType OutType) :
    MatchedTransformation -> IterType -> SourceModel -> (outputReferenceTypes InElTypes OutType (OutputPatternElementReference_getRefType o)).
  Proof.
    destruct o eqn:ho.
    exact o0.
  Defined.
  
  Definition OutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : string :=
    match o with 
      BuildOutputPatternElement _ _ y _ _ _ => y
    end.

  Definition OutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with 
      BuildOutputPatternElement _ _ _ y _ _ => y
    end.  

  Definition OutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (OutputPatternElement_getOutType o)) :=
    match o with 
      BuildOutputPatternElement _ _ _ _ y _ => y
    end.

  Definition OutputPatternElement_getOutputElementReferences {InElTypes: list SourceModelClass} {IterType: Type} (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
    match o with 
      BuildOutputPatternElement _ _ _ _ _ y => y
    end.

  Definition Rule_getName (x : Rule) : string :=
    match x with 
      BuildRule y _ _ _ _ _ => y
    end.

  Definition Rule_getInTypes (x : Rule) : list SourceModelClass :=
    match x with
      BuildRule _ y _ _ _ _ => y
    end.

  Definition Rule_getGuard (x : Rule) :
    SourceModel -> (guardTypes (Rule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition Rule_getIteratorType (x : Rule) : Type :=
    match x with
      BuildRule _ _ _ y _ _ => y
    end.
  
  Definition Rule_getIteratedList (x: Rule) :
    SourceModel -> (iteratedListTypes (Rule_getInTypes x) (Rule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.
  
  Definition Rule_getOutputPattern (x : Rule) :
    list (OutputPatternElement (Rule_getInTypes x) (Rule_getIteratorType x)) :=
    match x with
      BuildRule _ _ _ _ _ y => y
    end.

  Definition Rule_findOutputPatternElement (r: Rule) (name: string) : option (OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) :=
    find (fun(o:OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) => beq_string name (OutputPatternElement_getName o))
         (Rule_getOutputPattern r).
  
  Definition Transformation_getRules (x : Transformation) : list Rule :=
    match x with BuildTransformation y => y end.
  
  Definition MatchedOutputPatternElement_getName {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : string :=
    match o with 
      BuildMatchedOutputPatternElement _ _ y _ _ => y
    end.

  Definition MatchedOutputPatternElement_getOutType {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) : TargetModelClass :=
    match o with 
      BuildMatchedOutputPatternElement _ _ _ y _ => y
    end.  

  Definition MatchedOutputPatternElement_getOutPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (o: MatchedOutputPatternElement InElTypes IterType) :
    IterType -> SourceModel -> (outputPatternElementTypes InElTypes (MatchedOutputPatternElement_getOutType o)) :=
    match o with 
      BuildMatchedOutputPatternElement _ _ _ _ y => y
    end.

  Definition MatchedRule_getName (x : MatchedRule) : string :=
    match x with 
      BuildMatchedRule y _ _ _ _ _ => y
    end.

  Definition MatchedRule_getInTypes (x : MatchedRule) : list SourceModelClass :=
    match x with
      BuildMatchedRule _ y _ _ _ _ => y
    end.

  Definition MatchedRule_getGuard (x : MatchedRule) :
    SourceModel -> (guardTypes (MatchedRule_getInTypes x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.

  Definition MatchedRule_getIteratorType (x : MatchedRule) : Type :=
    match x with
      BuildMatchedRule _ _ _ y _ _ => y
    end.
  
  Definition MatchedRule_getIteratedList (x: MatchedRule) :
    SourceModel -> (iteratedListTypes (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)).
  Proof.
    destruct x eqn:hx.
    assumption.
  Defined.
  
  Definition MatchedRule_getOutputPattern (x : MatchedRule) :
    list (MatchedOutputPatternElement (MatchedRule_getInTypes x) (MatchedRule_getIteratorType x)) :=
    match x with
      BuildMatchedRule _ _ _ _ _ y => y
    end.
  
  Definition MatchedTransformation_getRules (x : MatchedTransformation) : list MatchedRule :=
    match x with BuildMatchedTransformation y => y end.

  (** ** Copying Matched Transformation *)
  
  Definition matchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: OutputPatternElement InElTypes IterType)
    : MatchedOutputPatternElement InElTypes IterType :=
    match x with
    | BuildOutputPatternElement _ _ c d e f => BuildMatchedOutputPatternElement InElTypes IterType c d e
    end.

  Definition matchRule (x: Rule) : MatchedRule :=
    match x with
    | BuildRule a b c d e f => BuildMatchedRule a b c d e (map matchOutputPatternElement f) 
    end.

  Definition matchTransformation (x: Transformation) : MatchedTransformation :=
    match x with
    | BuildTransformation a => BuildMatchedTransformation (map matchRule a) 
    end.

  Definition unmatchOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (x: MatchedOutputPatternElement InElTypes IterType)
    : OutputPatternElement InElTypes IterType :=
    match x with
    | BuildMatchedOutputPatternElement _ _ c d e => BuildOutputPatternElement InElTypes IterType c d e nil
    end.

  Definition unmatchRule (x: MatchedRule) : Rule :=
    match x with
    | BuildMatchedRule a b c d e f => BuildRule a b c d e (map unmatchOutputPatternElement f) 
    end.

  Definition unmatchTransformation (x: MatchedTransformation) : Transformation :=
    match x with
    | BuildMatchedTransformation a => BuildTransformation (map unmatchRule a) 
    end.

  (** * Semantics **)
  
  (** ** Expression Evaluation **)
  
  Definition evalGuard (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    evalFuncOfClasses smm sm (Rule_getInTypes r) bool (Rule_getGuard r) sp.
  
  Definition evalIterator (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    list (Rule_getIteratorType r) :=
    optionListToList
      (evalFuncOfClasses
         smm sm
         (Rule_getInTypes r) (list (Rule_getIteratorType r)) (Rule_getIteratedList r) sp).

  Definition evalOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (sm: SourceModel) (sp: list SourceModelElement) (iter: IterType) (o: OutputPatternElement InElTypes IterType) 
    : option TargetModelElement :=
    let val := 
        evalFuncOfClasses smm sm InElTypes (denoteModelClass (OutputPatternElement_getOutType o)) ((OutputPatternElement_getOutPatternElement o) iter) sp in
    match val with
    | None => None
    | Some r => Some (toModelElement (OutputPatternElement_getOutType o) r)
    end.

  Definition evalOutputPatternElementReference
             {InElTypes: list SourceModelClass} {IterType: Type} {TargetType: TargetModelClass}
             (sm: SourceModel) (sp: list SourceModelElement) (oe: TargetModelElement) (iter: IterType) (tr: MatchedTransformation)
             (o: OutputPatternElementReference InElTypes IterType TargetType) 
    : option TargetModelLink :=
    let val :=
    evalFuncOfClasses smm sm InElTypes ((denoteModelClass TargetType) -> option (denoteModelReference (OutputPatternElementReference_getRefType o)))
                      ((OutputPatternElementReference_getOutputReference o) tr iter) sp in
    match val with
    | None => None
    | Some r =>
      match toModelClass TargetType oe with
      | None => None
      | Some t => 
        match r t with
        | None => None
        | Some s => Some (toModelLink (OutputPatternElementReference_getRefType o) s)
        end
      end
    end.
 
  (** ** Rule application **)
  
  Definition matchRuleOnPattern (r: Rule) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuard r sm sp.

  Definition matchPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : list Rule :=
    filter (fun (r:Rule) =>
              match matchRuleOnPattern r sm sp with
              | (Some true) => true
              | _ => false end) (Transformation_getRules tr).

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i =>
          match (Rule_findOutputPatternElement r name) with
          | Some o =>  evalOutputPatternElement sm sp i o
          | None => None
          end
        | None => None
        end
      else
        None.
  
  Definition instantiateRuleOnPatternIter (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => 
             Some (optionList2List (map (evalOutputPatternElement sm sp i) (Rule_getOutputPattern r)))
        | None => None
        end
      else
        None.
  
  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (optionList2List (concat
                (map (fun f => map f (Rule_getOutputPattern r))
                     (map (evalOutputPatternElement sm sp) (evalIterator r sm sp)))))
      else
        None.

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => instantiateRuleOnPattern r sm sp) l)))
    end.

  Definition applyOutputPatternElementOnPatternIter
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink):=             
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i =>
          match (evalOutputPatternElement sm sp i ope) with
          | Some l => 
            Some (optionList2List (map ( fun (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope))
                        => evalOutputPatternElementReference sm sp l i (matchTransformation tr) oper
                      )
                      (OutputPatternElement_getOutputElementReferences ope)))
          | None => None
          end
        | None => None
        end
      else
        None.
  
  Definition applyRuleOnPatternIter (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => 
          Some (concat (optionList2List (map (fun x => applyOutputPatternElementOnPatternIter r x tr sm sp iter) (Rule_getOutputPattern r))))
        | None => None
        end
      else
        None.

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (concat (optionList2List (map (applyRuleOnPatternIter r tr sm sp) (indexes (length (evalIterator r sm sp))))))
      else
        None.

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (concat (optionList2List (map (fun r => applyRuleOnPattern r tr sm sp) l)))
    end.

  (** ** Resolution **)
  
  Definition resolveIter (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement) 
             (iter : nat) : option (denoteModelClass type) :=
    let tr := unmatchTransformation tr in
    let matchedRule := find (fun r:Rule =>
            match matchRuleOnPattern r sm sp with
            | Some true =>
              match nth_error (evalIterator r sm sp) iter with
              | Some x =>
                match Rule_findOutputPatternElement r name with
                | Some x => true
                | None => false
                end
              | None => false
              end
            | _ => false end)
                            (Transformation_getRules tr) in
    match matchedRule with
    | Some r => match instantiateRuleOnPatternIterName r sm sp iter name with
               | Some e => toModelClass type e
               | None => None
               end
    | None => None
    end.

  Definition resolve (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    resolveIter tr sm name type sp 0.

  Definition resolveAllIter (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
    : option (list (denoteModelClass type)) :=
    Some (optionList2List
            (map (fun l:(list SourceModelElement) => resolveIter tr sm name type l iter) sps)).
  
  Definition resolveAll (tr: MatchedTransformation) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) : option (list (denoteModelClass type)) :=
        resolveAllIter tr sm name type sps 0.
  
  (** ** Rule scheduling **)
  
  Definition maxArity (tr: Transformation) : nat :=
    max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr))).
    
  Definition allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))).

  (** * Certification **)

  Definition matchRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    matchRuleOnPattern r sm sp.

  Definition instantiateRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    instantiateRuleOnPattern r sm sp.

  (*Definition applyRuleOnPattern' (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
  *)  

  Theorem tr_execute_surj_elements : 
  forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (te : TargetModelElement),
   tm = execute tr sm -> In te (allModelElements tm) -> 
   (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
     instantiatePattern tr sm sp = Some tp /\
     incl sp (allModelElements sm) /\
     In te tp /\
     incl tp (allModelElements tm)).
  Proof.
    intros.
    rewrite H in H0.
    simpl in H0.
    apply concat_map_option_exists in H0.
    destruct H0.
    exists x.
    destruct H0.
    destruct (instantiatePattern tr sm x) eqn:inst.
    - exists l.
      split.
      + reflexivity.
      + unfold allTuples in H0.
        split. apply tuples_up_to_n_incl with (n:=(maxArity tr)). assumption.
        split. assumption.
        unfold execute in H.
        rewrite H. simpl.
        apply concat_map_option_incl with (a:=x).
        * assumption.
        * assumption.
    - contradiction.
  Qed.

  Theorem tr_instantiatePattern_surj_elements : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement),
      instantiatePattern tr sm sp = Some tp ->
      In te tp ->
      (exists (r : Rule) (tp1 : list TargetModelElement),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r sm sp = Some tp1 /\
          incl tp1 tp /\
          In te tp1).
  Proof.
    intros.
    unfold instantiatePattern in H.
    destruct (matchPattern tr sm sp) eqn:mtch.
    - inversion H.
    - Arguments optionList2List : simpl never.
      Arguments map : simpl never.
      inversion H.
      rewrite <- H2 in H0.
      apply concat_map_option_exists in H0.
      destruct H0.
      exists x.
      destruct H0.
      destruct (instantiateRuleOnPattern x sm sp) eqn:inst.
      + exists l0.
        split. assumption.
        split. reflexivity.
        split. apply concat_map_option_incl with (a:=x).
        * assumption.
        * assumption.
        * assumption.
      + contradiction.
  Qed.

  Theorem tr_instantiateRuleOnPattern_surj_elements : 
 forall (tr: Transformation) (sm : SourceModel) (tm : TargetModel) (sp: list SourceModelElement) (tp: list TargetModelElement) (te : TargetModelElement) (r : Rule),
  incl sp (allModelElements sm) ->
  incl tp (allModelElements tm) ->
  instantiateRuleOnPattern r sm sp = Some tp ->
  In te tp ->
   (In r (matchPattern tr sm sp) /\
    evalGuard r sm sp = Some true /\
    (exists (o: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (it: (Rule_getIteratorType r)),
        In it (evalIterator r sm sp) /\
        In o (Rule_getOutputPattern r) /\
        (evalOutputPatternElement sm sp it o) = Some te)).
  Proof.
  Admitted. 
  
  Theorem tr_match_pattern_derivable : 
    forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel),
      tm = execute tr sm ->
      forall (sp : list SourceModelElement)(r : Rule),
        In r (matchPattern tr sm sp) -> 
        matchRuleOnPattern' r tr sm sp = return true.
  Proof.
    intros.  
    unfold matchRuleOnPattern'.
    unfold matchPattern in H0.
    apply filter_In in H0.
    destruct H0.
    destruct (matchRuleOnPattern r sm sp).
    + destruct b.
      * reflexivity.
      * inversion H1.
    + inversion H1.
  Qed.

  Theorem tr_evalGuardFix_sp_gt_maxArity : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      (length sp) > (length (Rule_getInTypes r)) ->
      evalGuardFix (Rule_getInTypes r) (Rule_getGuard r sm) sp = None.
  Proof.
    intros.
    destruct r.
    simpl.

  Admitted.
      
  Theorem tr_matchPattern_sp_nil : 
    forall (tr: Transformation) (sm : SourceModel),
      (matchPattern tr sm nil) = nil.
  Proof.
    intros.
    unfold matchPattern.
    induction (Transformation_getRules tr).
    - auto.
    - simpl.
      unfold matchRuleOnPattern.
      unfold evalGuard.
      assert (evalGuardFix (Rule_getInTypes a) (Rule_getGuard a sm) nil = None).
      { apply tr_evalGuardFix_sp_nil. }
      rewrite H.
      apply IHl.
  Qed.
  
  Theorem tr_matchPattern_sp_gt_maxArity : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      (length sp) > (maxArity tr) ->
      (matchPattern tr sm sp) = nil.
  Proof.
    intros.
    unfold matchPattern.
    unfold matchRuleOnPattern.
    unfold evalGuard.
    destruct tr.
    induction l.
    - simpl; auto.
    - assert (length sp > length (Rule_getInTypes a)).
      { assert (maxArity (BuildTransformation (a :: l)) >= length (Rule_getInTypes a) ).
        { apply  max_list_upperBound. crush. }
        crush. }
      assert (evalGuardFix  (Rule_getInTypes a) (Rule_getGuard a sm) sp = None).
      { apply tr_evalGuardFix_sp_gt_maxArity. exact H0. }
      simpl.
      rewrite H1.
      apply IHl.
      unfold maxArity in H.
      simpl in H.
      case ( ble_nat (Datatypes.length (Rule_getInTypes a))
          (max (map (Datatypes.length (A:=SourceModelClass)) (map Rule_getInTypes l)))) eqn: ca_max.
      -- crush.
      -- apply ble_nat_false in ca_max.
         unfold maxArity.
         simpl.
         crush.
  Qed.      

      
  Instance CoqTLEngine : 
    TransformationEngine Transformation Rule SourceModelElement SourceModelLink TargetModelElement TargetModelLink := 
    {
      getRules := Transformation_getRules;
      execute := execute;
      
      matchPattern := matchPattern;
      instantiatePattern := instantiatePattern;
      applyPattern := applyPattern;
      matchRuleOnPattern := matchRuleOnPattern';
      instantiateRuleOnPattern := instantiateRuleOnPattern';
      applyRuleOnPattern := applyRuleOnPattern;
      match_pattern_derivable :=  tr_match_pattern_derivable; (*
      instantiate_pattern_derivable :=  tr_instantiate_pattern_derivable;
      apply_pattern_derivable :=  tr_apply_pattern_derivable; 
      tr_surj_elements := tr_surj_elements;
      tr_surj_links := tr_surj_links;
      outp_incl_elements := outp_incl_elements;
      outp_incl_links := outp_incl_links;
      match_in := match_incl;
      match_functional := match_functional;*)
    }.

  
End CoqTL.

Arguments MatchedTransformation: default implicits.


Arguments BuildTransformation
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildRule
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _.
Arguments BuildOutputPatternElement
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType].
Arguments BuildOutputPatternElementReference
          [SourceModelElement] [SourceModelLink] [SourceModelClass] [SourceModelReference] _
          [TargetModelElement] [TargetModelLink] [TargetModelClass] [TargetModelReference] _
          _ [IterType]. 

Arguments resolveIter: default implicits.
Arguments resolve: default implicits.
Arguments resolveAllIter: default implicits.
Arguments resolveAll: default implicits.


Arguments execute: default implicits.
Arguments matchPattern: default implicits.
Arguments instantiatePattern: default implicits.
Arguments instantiateRuleOnPattern: default implicits.
Arguments evalGuard: default implicits.
Arguments evalIterator: default implicits.
Arguments evalOutputPatternElement: default implicits.

Arguments Transformation: default implicits.
Arguments Transformation_getRules: default implicits.
Arguments maxArity: default implicits.

Arguments Rule: default implicits.
Arguments Rule_getInTypes: default implicits.
Arguments Rule_getIteratorType: default implicits.
Arguments Rule_getOutputPattern: default implicits.

Arguments OutputPatternElement: default implicits.
Arguments OutputPatternElement_getOutType: default implicits.
Arguments OutputPatternElement_getOutPatternElement: default implicits.
