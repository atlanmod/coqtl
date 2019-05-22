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
    denoteFunction smm (sclasses) ((denoteModelClass tclass) -> option (denoteModelReference tref)).
  
  Definition outputPatternElementTypes
             (sclasses : list SourceModelClass) (tclass: TargetModelClass) :=
    denoteFunction smm (sclasses) (denoteModelClass tclass).

  Definition iteratedListTypes
             (sclasses : list SourceModelClass) (itype: Type) :=
    denoteFunction smm (sclasses) (list itype).

  Definition guardTypes (sclasses : list SourceModelClass) :=
    denoteFunction smm (sclasses) bool.

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
    evalFunction smm sm (Rule_getInTypes r) bool (Rule_getGuard r) sp.
  
  Definition evalIterator (r : Rule) (sm: SourceModel) (sp: list SourceModelElement) :
    list (Rule_getIteratorType r) :=
    optionListToList
      (evalFunction
         smm sm
         (Rule_getInTypes r) (list (Rule_getIteratorType r)) (Rule_getIteratedList r) sp).

  Definition evalOutputPatternElement {InElTypes: list SourceModelClass} {IterType: Type} (sm: SourceModel) (sp: list SourceModelElement) (iter: IterType) (o: OutputPatternElement InElTypes IterType) 
    : option TargetModelElement :=
    let val := 
        evalFunction smm sm InElTypes (denoteModelClass (OutputPatternElement_getOutType o)) ((OutputPatternElement_getOutPatternElement o) iter) sp in
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
        evalFunction smm sm InElTypes ((denoteModelClass TargetType) -> option (denoteModelReference (OutputPatternElementReference_getRefType o)))
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

  Definition instantiateElementOnPattern (r: Rule) (o: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat)
    : option TargetModelElement :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i => evalOutputPatternElement sm sp i o
        | None => None
        end
      else
        None.
  
  Definition instantiateIterationOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun o => optionToList (instantiateElementOnPattern r o sm sp iter))
                       (Rule_getOutputPattern r))
      else
        None.
  
  Definition instantiateRuleOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun i:nat => optionListToList (instantiateIterationOnPattern r sm sp i))
                       (indexes (length (evalIterator r sm sp))))
      else
        None.

  Definition instantiatePattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (flat_map (fun r => optionListToList (instantiateRuleOnPattern r sm sp)) l)
    end.

  Definition instantiateRuleOnPatternIterName (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) (name: string): option (TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (Rule_findOutputPatternElement r name) with
        | Some o =>  instantiateElementOnPattern r o sm sp iter
        | None => None
        end
      else
        None.

  Definition instantiateElementsOnPattern (r: Rule) (sm: SourceModel) (sp: list SourceModelElement) (name: string) : option (list TargetModelElement) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun it : nat => optionToList (instantiateRuleOnPatternIterName r sm sp it name))
                       (indexes (length (evalIterator r sm sp))))
      else
        None.

  Definition applyReferenceOnPattern
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option TargetModelLink :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        match (nth_error (evalIterator r sm sp) iter) with
        | Some i =>
          match (evalOutputPatternElement sm sp i ope) with
          | Some l => evalOutputPatternElementReference sm sp l i (matchTransformation tr) oper
          | None => None
          end
        | None => None
        end
      else
        None.
  
  Definition applyElementOnPattern
             (r: Rule)
             (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
             (tr: Transformation)
             (sm: SourceModel)
             (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink):=             
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map ( fun oper => optionToList (applyReferenceOnPattern r ope oper tr sm sp iter))
                       (OutputPatternElement_getOutputElementReferences ope))
      else
        None.

  Definition applyIterationOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun x => optionListToList (applyElementOnPattern r x tr sm sp iter))
                       (Rule_getOutputPattern r))
      else
        None.

  Definition applyRuleOnPattern (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (flat_map (fun i:nat => optionListToList (applyIterationOnPattern r tr sm sp i))
                       (indexes (length (evalIterator r sm sp))))
      else
        None.

  Definition applyPattern (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    match matchPattern tr sm sp with
    | nil => None
    | l => Some (flat_map (fun r => optionListToList (applyRuleOnPattern r tr sm sp)) l)
    end.

  Definition applyElementsOnPattern (r: Rule) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    m <- matchRuleOnPattern r sm sp;
      if m then
        Some (concat (flat_map (fun iter => optionToList (applyElementOnPattern r ope tr sm sp iter))
                               (indexes (length (evalIterator r sm sp)))))
      else
        None.

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
    Some (flat_map (fun l:(list SourceModelElement) => optionToList (resolveIter tr sm name type l iter)) sps).
  
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
      (flat_map (fun t => optionListToList (instantiatePattern tr sm t)) (allTuples tr sm))
      (flat_map (fun t => optionListToList (applyPattern tr sm t)) (allTuples tr sm)).

  (** * Certification **)
  
  Definition matchRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    matchRuleOnPattern r sm sp.

  Definition instantiateRuleOnPattern' (r: Rule) (t: Transformation) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    instantiateRuleOnPattern r sm sp.

  Definition applyRuleOnPattern' (r: Rule) (tr: Transformation) (sm: SourceModel) (sp: list SourceModelElement): option (list TargetModelLink) :=
    applyRuleOnPattern r tr sm sp.

  Definition OutputPatternElement_getOutType' (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) : TargetModelClass :=
    OutputPatternElement_getOutType o.

  Definition OutputPatternElement_getOutputElementReferences' (InElTypes: list SourceModelClass) (IterType: Type) (o: OutputPatternElement InElTypes IterType) :
    list (OutputPatternElementReference InElTypes IterType (OutputPatternElement_getOutType o)) :=
    OutputPatternElement_getOutputElementReferences o.
  
  (** ** execute **)
  
  Theorem tr_execute_in_elements : 
    forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) <->
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (allModelElements sm) /\
          instantiatePattern tr sm sp = Some tp /\
          In te tp).
  Proof.
    (*intros.
    split.
    - intros.
      simpl in H.
      apply concat_map_option_exists in H.
      destruct H.
      exists x.
      destruct H.
      destruct (instantiatePattern tr sm x) eqn:inst.
      + exists l.
        split. 
        unfold allTuples in H.
        apply tuples_up_to_n_incl with (n:=(maxArity tr)). assumption.
        split. reflexivity.
        assumption.
      + contradiction.
    - intros.
      destruct H. destruct H. destruct H. destruct H0.
      unfold execute. simpl.
      apply concat_in with (l0:=x0).
      + assumption.
      + unfold instantiatePattern in H0.
        destruct (matchPattern tr sm x) eqn:mtch.
        * inversion H0.
        * unfold matchPattern in mtch.*)
  Admitted.

  Theorem tr_execute_in_links : 
    forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
      In tl (allModelLinks (execute tr sm)) <->
      (exists (sp : list SourceModelElement) (tpl : list TargetModelLink),
          incl sp (allModelElements sm) /\
          applyPattern tr sm sp = Some tpl /\
          In tl tpl).
  Proof.
  Admitted.
  
  (** ** instantiatePattern **)

  Theorem tr_instantiatePattern_in : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      (exists tp: list TargetModelElement, instantiatePattern tr sm sp = Some tp /\
       In te tp) <->
      (exists (r : Rule) (tp1 : list TargetModelElement),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r sm sp = Some tp1 /\
          In te tp1).
  Proof.
   split.
    - intros.
      unfold instantiatePattern in H.
      destruct (matchPattern tr sm sp) eqn:mtch.
      + inversion H. inversion H0. inversion H1.
      + remember (r::l) as l1.
        destruct H.
        inversion H. inversion H0.
        rewrite <- H3 in H1.
        apply in_flat_map in H1.
        destruct H1.
        exists x0.
        destruct H1.
        destruct (instantiateRuleOnPattern x0 sm sp) eqn:inst.
        exists l0.
        split. assumption.
        split. reflexivity.
        assumption.
        contradiction.
    - intros.
      destruct (instantiatePattern tr sm sp) eqn:inst.
      + exists l. split. reflexivity.
        unfold instantiatePattern in inst.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * inversion inst.
        * Arguments optionListToList : simpl never.
          Arguments flat_map : simpl never.
          inversion inst.
          apply in_flat_map.
          destruct H. destruct H. destruct H. destruct H0.
          exists x. split. assumption.
          unfold optionListToList.
          rewrite H0.
          assumption.
      + exfalso.
        destruct H. destruct H. destruct H. destruct H0.
        unfold instantiatePattern in inst.
        destruct (matchPattern tr sm sp) eqn:mtch.
        * contradiction.
        * inversion inst.
  Qed.

  Theorem tr_instantiatePattern_maxArity : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      instantiatePattern tr sm sp = None.
  Proof.
  Admitted.

  (** ** instantiateRuleOnPattern **)
    
  Theorem tr_instantiateRuleOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      (exists tp: list TargetModelElement, instantiateRuleOnPattern' r tr sm sp = Some tp /\
       In te tp) <->
      (exists (i: nat) (tp1: list TargetModelElement),
          i < length (evalIterator r sm sp) /\
          instantiateIterationOnPattern r sm sp i = Some tp1 /\
          In te tp1).
  Proof.
    split.
    - intros.
      unfold instantiateRuleOnPattern' in H.
      unfold instantiateRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
        * Arguments optionList2List : simpl never.
          Arguments map : simpl never.
          inversion H.
          inversion H0.
          inversion H1.
          rewrite <- H4 in H2.
          apply concat_map_option_exists in H2.
          destruct H2.
          destruct H2.
          destruct (instantiateRuleOnPatternIter r sm sp x0) eqn:inst_ca.
          ** exists x0.
             exists l.
             split.
             *** apply indexes_nat_upperBound.
                 exact H2.
             *** split; crush.         
          ** contradiction.
        * inversion H.
          destruct H0.
          inversion H0.        
      + crush.
    - admit.
  Admitted.

  Theorem tr_instantiateRuleOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      length sp <> length (Rule_getInTypes r) ->
      instantiateRuleOnPattern' r tr sm sp = None.
  Proof.
  Admitted.

  (** ** instantiateIterationOnPattern **)

  Theorem tr_instantiateIterationOnPattern_in : 
    forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
      (exists tp: list TargetModelElement, instantiateIterationOnPattern r sm sp i = Some tp /\
       In te tp) <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
          In ope (Rule_getOutputPattern r) /\ 
          instantiateElementOnPattern r ope sm sp i = Some te).
  Proof.
    split.
    - intros.
      unfold instantiateRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
  Admitted.

  Theorem tr_instantiateIterationOnPattern_inTypes : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      length sp <> length (Rule_getInTypes r) ->
      instantiateIterationOnPattern r sm sp i = None.
  Proof.
  Admitted.

  Theorem tr_instantiateIterationOnPattern_iterator : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      instantiateIterationOnPattern r sm sp i = None.
  Proof.
  Admitted.
  
  (** ** instantiateElementOnPattern **)

  Theorem tr_instantiateElementOnPattern_inTypes : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      length sp <> length (Rule_getInTypes r) ->
      instantiateElementOnPattern r ope sm sp i = None.
  Proof.
  Admitted.

  Theorem tr_instantiateElementOnPattern_iterator : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      instantiateElementOnPattern r ope sm sp i = None.
  Proof.
  Admitted.
  
  (** ** applyPattern **)

  Theorem tr_applyPattern_in : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
      (exists tpl: list TargetModelLink, applyPattern tr sm sp = Some tpl /\
       In tl tpl) <->
      (exists (r : Rule) (tpl1 : list TargetModelLink),
          In r (matchPattern tr sm sp) /\
          applyRuleOnPattern r tr sm sp = Some tpl1 /\
          In tl tpl1).
  Proof.
  Admitted.

  Theorem tr_applyPattern_maxArity : 
    forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      length sp > maxArity tr ->
      applyPattern tr sm sp = None.
  Proof.
  Admitted.

  (** ** applyRuleOnPattern **)

  Theorem tr_applyRuleOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
      (exists tpl: list TargetModelLink, applyRuleOnPattern' r tr sm sp = Some tpl /\
       In tl tpl) <->
      (exists (i: nat) (tpl1: list TargetModelLink),
          i < length (evalIterator r sm sp) /\
          applyIterationOnPattern r tr sm sp i = Some tpl1 /\
          In tl tpl1).
  Proof.
  Admitted.

  Theorem tr_applyRuleOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      length sp <> length (Rule_getInTypes r) ->
      applyRuleOnPattern' r tr sm sp = None.
  Proof.
  Admitted.

  (** ** applyIterationOnPattern **)

  Theorem tr_applyIterationOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
      (exists tpl: list TargetModelLink, applyIterationOnPattern r tr sm sp i = Some tpl /\
       In tl tpl) <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)) (tpl1: list TargetModelLink),
          In ope (Rule_getOutputPattern r) /\ 
          applyElementOnPattern r ope tr sm sp i = Some tpl1 /\
          In tl tpl1).
  Proof.
    split.
    - intros.
      unfold instantiateRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
  Admitted.

  Theorem tr_applyIterationOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      length sp <> length (Rule_getInTypes r) ->
      applyIterationOnPattern r tr sm sp i = None.
  Proof.
  Admitted.

  Theorem tr_applyIterationOnPattern_iterator : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat),
      i >= length (evalIterator r sm sp) ->
      applyIterationOnPattern r tr sm sp i = None.
  Proof.
  Admitted.
  
  (** ** applyElementOnPattern **)

  Theorem tr_applyElementOnPattern_in : 
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      (exists tpl: list TargetModelLink, applyElementOnPattern r ope tr sm sp i = Some tpl /\
       In tl tpl) <->
      (exists (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
          In ope (Rule_getOutputPattern r) /\ 
          applyReferenceOnPattern r ope oper tr sm sp i = Some tl).
  Proof.
    split.
    - intros.
      unfold instantiateRuleOnPattern in H.
      destruct (matchRuleOnPattern r sm sp) eqn:mtch.
      + destruct b.
  Admitted.

  Theorem tr_applyElementOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      length sp <> length (Rule_getInTypes r) ->
      applyElementOnPattern r ope tr sm sp i = None.
  Proof.
  Admitted.

  Theorem tr_applyElementOnPattern_iterator : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat) (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r)),
      i >= length (evalIterator r sm sp) ->
      applyElementOnPattern r ope tr sm sp i = None.
  Proof.
  Admitted.

  (** ** applyReferenceOnPattern **)

  Theorem tr_applyReferenceOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
      (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
      length sp <> length (Rule_getInTypes r) ->
      applyReferenceOnPattern r ope oper tr sm sp i = None.
  Proof.
  Admitted.

  Theorem tr_applyReferenceOnPattern_iterator : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
      (ope: OutputPatternElement (Rule_getInTypes r) (Rule_getIteratorType r))
      (oper: OutputPatternElementReference (Rule_getInTypes r) (Rule_getIteratorType r) (OutputPatternElement_getOutType ope)),
      i >= length (evalIterator r sm sp) ->
      applyReferenceOnPattern r ope oper tr sm sp i = None.
  Proof.
  Admitted.

  (** ** matchPattern **)

  Theorem tr_matchPattern_in : 
    forall (tr: Transformation) (sm : SourceModel),
    forall (sp : list SourceModelElement)(r : Rule),
      In r (matchPattern tr sm sp) <->
      In r (Transformation_getRules tr) /\
      matchRuleOnPattern' r tr sm sp = return true.
  Proof.
    intros.
    split.
    - intros.
      unfold matchRuleOnPattern'.
      unfold matchPattern in H.
      apply filter_In in H.
      destruct H.
      destruct (matchRuleOnPattern r sm sp).
      + destruct b.
        * split. assumption. reflexivity.
        * inversion H0.
      + inversion H0.
    - intros.
      destruct H.
      unfold matchPattern.
      apply <- filter_In.
      split. assumption.
      unfold matchRuleOnPattern' in H0.
      rewrite H0.
      reflexivity.
  Qed.

  (** ** matchRuleOnPattern **)

  (* Theorem tr_matchRuleOnPattern_eval : 
    forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      matchRuleOnPattern r sm sp = 
      evalFunction smm sm (Rule_getInTypes r) bool (Rule_getGuard r) sp.
  Proof.
    crush.
  Qed. *)
  
  Theorem tr_matchRuleOnPattern_inTypes : 
    forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      length sp <> length (Rule_getInTypes r) ->
      matchRuleOnPattern' r tr sm sp = None.
  Proof.
  Admitted.
    
  (** * Typeclass instantiation **)
      
  Instance CoqTLEngine : 
    TransformationEngine := 
    {
      SourceModelElement := SourceModelElement;
      SourceModelClass := SourceModelClass;
      SourceModelLink := SourceModelLink;
      SourceModelReference := SourceModelReference;
      TargetModelElement := TargetModelElement;
      TargetModelClass := TargetModelClass;
      TargetModelLink := TargetModelLink;
      TargetModelReference := TargetModelReference;

      Transformation := Transformation;
      Rule := Rule;
      OutputPatternElement := OutputPatternElement;
      OutputPatternElementReference := OutputPatternElementReference;
            
      getRules := Transformation_getRules;
      getInTypes := Rule_getInTypes;
      getIteratorType := Rule_getIteratorType;
      getOutputPattern := Rule_getOutputPattern;
      getOutType := OutputPatternElement_getOutType';
      getOutputElementReferences := OutputPatternElement_getOutputElementReferences';
      
      execute := execute;
      matchPattern := matchPattern;
      instantiatePattern := instantiatePattern;
      applyPattern := applyPattern;
      
      matchRuleOnPattern := matchRuleOnPattern';
      instantiateRuleOnPattern := instantiateRuleOnPattern';
      applyRuleOnPattern := applyRuleOnPattern';

      instantiateIterationOnPattern := instantiateIterationOnPattern;
      applyIterationOnPattern := applyIterationOnPattern;

      instantiateElementOnPattern := instantiateElementOnPattern;
      applyElementOnPattern := applyElementOnPattern;

      applyReferenceOnPattern := applyReferenceOnPattern;
      
      evalIterator := evalIterator;
        
      tr_execute_in_elements := tr_execute_in_elements;
      tr_execute_in_links := tr_execute_in_links;
      
      tr_instantiatePattern_in := tr_instantiatePattern_in;
      tr_instantiatePattern_maxArity := tr_instantiatePattern_maxArity;

      tr_instantiateRuleOnPattern_in := tr_instantiateRuleOnPattern_in;
      tr_instantiateRuleOnPattern_inTypes := tr_instantiateRuleOnPattern_inTypes;

      tr_instantiateIterationOnPattern_in := tr_instantiateIterationOnPattern_in;
      tr_instantiateIterationOnPattern_inTypes := tr_instantiateIterationOnPattern_inTypes;
      tr_instantiateIterationOnPattern_iterator := tr_instantiateIterationOnPattern_iterator;

      tr_instantiateElementOnPattern_inTypes := tr_instantiateElementOnPattern_inTypes;
      tr_instantiateElementOnPattern_iterator := tr_instantiateElementOnPattern_iterator;
      
      tr_applyPattern_in := tr_applyPattern_in;
      tr_applyPattern_maxArity := tr_applyPattern_maxArity;

      tr_applyRuleOnPattern_in := tr_applyRuleOnPattern_in;
      tr_applyRuleOnPattern_inTypes := tr_applyRuleOnPattern_inTypes;

      tr_applyIterationOnPattern_in := tr_applyIterationOnPattern_in;
      tr_applyIterationOnPattern_inTypes := tr_applyIterationOnPattern_inTypes;
      tr_applyIterationOnPattern_iterator := tr_applyIterationOnPattern_iterator;

      tr_applyElementOnPattern_in := tr_applyElementOnPattern_in;
      tr_applyElementOnPattern_inTypes := tr_applyElementOnPattern_inTypes;
      tr_applyElementOnPattern_iterator := tr_applyElementOnPattern_iterator;

      tr_applyReferenceOnPattern_inTypes := tr_applyReferenceOnPattern_inTypes;
      tr_applyReferenceOnPattern_iterator := tr_applyReferenceOnPattern_iterator;
      
      tr_matchPattern_in := tr_matchPattern_in;
      
      tr_matchRuleOnPattern_inTypes := tr_matchRuleOnPattern_inTypes;
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
