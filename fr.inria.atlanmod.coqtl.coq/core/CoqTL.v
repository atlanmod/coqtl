Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.tTop.
Require Import core.utils.tList.

Set Implicit Arguments.

Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.

  Definition SourceMetamodel_toEObject (c : SourceModelElement) : SourceModelElement := c.
  
  (** * Concrete Syntax

  Example: 
        rule Attribute2Column
        from                    -- InputPatternElement
          a : Attribute         -- Element Definition
            a.name = "father"     -- Guard
        to [                    -- OutputPatternElement
          output "t":           -- elem_id
            c : Column          -- elem_name : elem_type
              t.name <- a.name
              t.id   <- a.id
          references:           -- ref_def
            Column * Table      -- ref_type   
            M                   -- trg_instance -> help resolving
            :=                  -- ref_ends -> specify how to construct ref_def
            y' <- a.class;
            y <- resolve(a.class);
            BuildRef c y
         ]
   **)

  (** ** OutputPatternElementReference **)

  (* Build OutputPatternElementReference with :
      an ref_type
      an trg_instance
      and a ref_ends         
   *)
  Inductive OutputPatternElementReference : Type :=
  | BuildOutputPatternElementReference : forall (OutRefs: TargetModelReference),
      (option (denoteModelReference OutRefs))
      -> OutputPatternElementReference.

  Definition OutputPatternElementReferenceType (o :  OutputPatternElementReference) : TargetModelReference :=
    match o with
      (BuildOutputPatternElementReference type link) => type
    end.
                                                                                       
  Definition OutputPatternElementReferenceLink (o :  OutputPatternElementReference) : option TargetModelLink :=
    match o with
      (BuildOutputPatternElementReference type link) =>
      ml <- link;
      return toModelLink type ml
    end.
  
  Fixpoint getOutputPatternElementReferenceTargetModelLinks (l : list OutputPatternElementReference) : list TargetModelLink :=
    match l with
    | nil => nil
    | ope :: opel => match ope with
                    | BuildOutputPatternElementReference OutRefs x =>
                      match x with
                      | Some x => BuildModelLink OutRefs x :: getOutputPatternElementReferenceTargetModelLinks opel
                      | None => getOutputPatternElementReferenceTargetModelLinks opel
                      end
                    end
    end.

  (** ** OutputPatternElement **)

  (* Build OutputPatternElement with :
      an elem_type
      an elem_id
      an elem_def
      and a (elem_name->ref_def)
   *)
  Inductive OutputPatternElement : Type :=
  | BuildOutputPatternElement : forall (OutElType: TargetModelClass),
      string
      -> (denoteModelClass OutElType)
      -> ((denoteModelClass OutElType) -> list OutputPatternElementReference)
      -> OutputPatternElement.
  
  Definition getOutputPatternElementName (o :  OutputPatternElement) : string :=
    match o with
      (BuildOutputPatternElement type name el refs) => name
    end.

  Definition getOutputPatternElementType (o :  OutputPatternElement) : TargetModelClass :=
    match o with
      (BuildOutputPatternElement type name el refs) => type
    end.

  Definition getOutputPatternElementBindings (o :  OutputPatternElement) : ((denoteModelClass (getOutputPatternElementType o)) -> list OutputPatternElementReference) :=
    match o with
      (BuildOutputPatternElement type name el refs) => refs
    end.

  Definition getOutputPatternElementElementType (o :  OutputPatternElement) : Set :=
    match o with
      (BuildOutputPatternElement type name el refs) => denoteModelClass type
    end.

  Definition getOutputPatternElementElement (o :  OutputPatternElement) : getOutputPatternElementElementType o :=
    match o with
      (BuildOutputPatternElement type name el refs) => el
    end.
  
  Definition getOutputPatternElementTargetModelElement (o :  OutputPatternElement) : TargetModelElement :=
    match o with
    | BuildOutputPatternElement OutElType x x0 x1 => toModelElement OutElType x0
    end.

  Definition getOutputPatternElementTargetModelLinks (o :  OutputPatternElement): list TargetModelLink :=
    match o with
      (BuildOutputPatternElement type name el refs) => getOutputPatternElementReferenceTargetModelLinks (refs el)
    end.

  Definition getOutputPatternElementElementByType (o :  OutputPatternElement) (type: TargetModelClass) : option (denoteModelClass type).
  Proof.
    remember o as ope.
    destruct o.
    remember (eqModelClass_dec type OutElType) as equal.
    destruct equal.
    - rewrite e.
      exact (Some d).
    - exact None.
  Defined.

  Inductive Rule: Type :=
  | BuildMultiElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> Rule)
        -> Rule
  | BuildSingleElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> (bool * list OutputPatternElement))
        -> Rule.

  Definition Phase : Type := SourceModel -> list Rule.

  Definition Transformation : Type := Phase -> Phase.

  (** * Abstract Syntax **)

  Inductive OutputBindingExpressionA : Type :=
      BuildOutputBindingExpressionA :
        nat ->
        nat ->
        nat ->
        OutputBindingExpressionA.

  Definition OutputBindingExpressionA_getRule (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA y _ _ => y end.
  
  Definition OutputBindingExpressionA_getOutputPatternElement (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ y _ => y end.

  Definition OutputBindingExpressionA_getOutputBinding (x : OutputBindingExpressionA) : nat :=
    match x with BuildOutputBindingExpressionA _ _ y => y end.
  
  Inductive OutputPatternElementReferenceA : Type :=
      BuildOutputPatternElementReferenceA :
        TargetModelReference ->
        OutputBindingExpressionA -> 
        OutputPatternElementReferenceA.

  Definition OutputPatternElementReferenceA_getType (x : OutputPatternElementReferenceA) : TargetModelReference :=
    match x with BuildOutputPatternElementReferenceA y _ => y end. 
  
  Definition OutputPatternElementReferenceA_getOutputBindingExpression (x : OutputPatternElementReferenceA) : OutputBindingExpressionA :=
    match x with BuildOutputPatternElementReferenceA _ y => y end. 

  Inductive OutputPatternElementExpressionA : Type :=
    BuildOutputPatternElementExpressionA :
      nat ->
      nat ->
      OutputPatternElementExpressionA.

  Definition OutputPatternElementExpressionA_getRule (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA y _ => y end.

  Definition OutputPatternElementExpressionA_getOutputPatternElement (x : OutputPatternElementExpressionA) : nat :=
    match x with BuildOutputPatternElementExpressionA _ y => y end.
  
  Inductive OutputPatternElementA : Type := 
    BuildOutputPatternElementA :
      string ->
      TargetModelClass ->
      OutputPatternElementExpressionA ->
      list OutputPatternElementReferenceA -> OutputPatternElementA.

  Definition OutputPatternElementA_getName (x : OutputPatternElementA) : string :=
    match x with BuildOutputPatternElementA y _ _ _  => y end.

  Definition OutputPatternElementA_getType (x : OutputPatternElementA) : TargetModelClass :=
    match x with BuildOutputPatternElementA _ y _ _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementExpression (x : OutputPatternElementA) : OutputPatternElementExpressionA :=
    match x with BuildOutputPatternElementA _ _ y _  => y end.

  Definition OutputPatternElementA_getOutputPatternElementReferences (x : OutputPatternElementA) : list OutputPatternElementReferenceA :=
    match x with BuildOutputPatternElementA _ _ _ y  => y end.

  Inductive GuardExpressionA : Type :=
    BuildGuardExpressionA :
      nat ->
      GuardExpressionA.

  Definition GuardExpressionA_getRule (x : GuardExpressionA) : nat :=
    match x with BuildGuardExpressionA y => y end.
  
  Inductive RuleA : Type := 
    BuildRuleA :
      list SourceModelClass ->
      GuardExpressionA ->
      list OutputPatternElementA -> RuleA.

  Definition RuleA_getInTypes (x : RuleA) : list SourceModelClass :=
    match x with BuildRuleA y _ _ => y end.

  Definition RuleA_getGuard (x : RuleA) : GuardExpressionA :=
    match x with BuildRuleA _ y _ => y end.

  Definition RuleA_getOutputPattern (x : RuleA) : list OutputPatternElementA :=
    match x with BuildRuleA _ _ y => y end.  
  
  Inductive TransformationA : Type := 
    BuildTransformationA :
      list RuleA ->
      Transformation ->
      TransformationA.

  Definition TransformationA_getTransformation (x : TransformationA) : Transformation :=
    match x with BuildTransformationA _ y => y end.

  Definition TransformationA_getRules (x : TransformationA) : list RuleA :=
    match x with BuildTransformationA y _ => y end.

  (** * Parser **)
  
  Definition parseOutputPatternElementReference (tr: Transformation) (r ope oper: nat) (o: OutputPatternElementReference) : OutputPatternElementReferenceA :=   
    match o with
    | BuildOutputPatternElementReference t _ =>
      BuildOutputPatternElementReferenceA t (BuildOutputBindingExpressionA r ope oper)
    end.

  Definition parseOutputPatternElement (tr: Transformation) (r ope: nat) (o: OutputPatternElement) : OutputPatternElementA :=   
    match o with
    | BuildOutputPatternElement t n _ f =>
      BuildOutputPatternElementA n t (BuildOutputPatternElementExpressionA r ope) (mapWithIndex (parseOutputPatternElementReference tr r ope) 0 (f (bottomModelClass t)))
    end.

  Fixpoint parseRuleOutput (tr: Transformation) (n: nat) (r: Rule) : list OutputPatternElementA :=
    match r with
    | BuildMultiElementRule iet f => parseRuleOutput tr n (f (bottomModelClass iet)) 
    | BuildSingleElementRule iet f => mapWithIndex (parseOutputPatternElement tr n) 0 (snd (f (bottomModelClass iet))) 
    end.    
  
  Fixpoint parseRuleTypes (r: Rule) : list SourceModelClass :=
    match r with
    | BuildMultiElementRule iet f => (cons iet (parseRuleTypes (f (bottomModelClass iet))))
    | BuildSingleElementRule iet f => iet::nil
    end.
  
  Definition parseRule (tr: Transformation) (n: nat) (r: Rule) : RuleA :=
    (BuildRuleA (parseRuleTypes r) (BuildGuardExpressionA n) (parseRuleOutput tr n r)).

  Definition parseTransformation (tr: Transformation) : TransformationA :=
    BuildTransformationA 
      (mapWithIndex (parseRule tr) 0 (tr (fun c:SourceModel => nil) (BuildModel nil nil) )) tr.

  (** * Expression Evaluation **)

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputBindingExpressionA' (o : OutputBindingExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) (te: TargetModelElement) : option TargetModelLink :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputBindingExpressionA' o (f e') ts sm els te
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputBindingExpressionA_getOutputPatternElement o));
        te' <- toModelClass (getOutputPatternElementType ope) te;
        oper <- (nth_error ((getOutputPatternElementBindings ope) te') (OutputBindingExpressionA_getOutputBinding o));
        (OutputPatternElementReferenceLink oper)
    | _, _, _ => None
    end.
  
  Definition evalOutputBindingExpressionA (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) (o : OutputBindingExpressionA) : option (TargetModelLink) :=
  r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputBindingExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputBindingExpressionA_getRule o));
  evalOutputBindingExpressionA' o r (RuleA_getInTypes ra) sm sp te. 

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputPatternElementExpressionA' (o : OutputPatternElementExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option TargetModelElement :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputPatternElementExpressionA' o (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputPatternElementExpressionA_getOutputPatternElement o));
        return (getOutputPatternElementTargetModelElement ope)
    | _, _, _ => None
    end.
  
  Definition evalOutputPatternElementExpressionA (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (o : OutputPatternElementExpressionA): option TargetModelElement :=
  r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputPatternElementExpressionA_getRule o));
  evalOutputPatternElementExpressionA' o r (RuleA_getInTypes ra) sm sp. 

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalGuardExpressionA' (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option bool :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalGuardExpressionA' (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
      return (fst (f e'))
    | _, _, _ => None
    end.
  
  Definition evalGuardExpressionA (o : GuardExpressionA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (GuardExpressionA_getRule o));
      ra <- (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule o));
  evalGuardExpressionA' r (RuleA_getInTypes ra) sm sp. 

  (** * Engine **)

  (** ** Rule application **)

  Inductive ModelFragment (ModelElement: Type) (ModelLink: Type): Type :=
    BuildModelFragment: list ModelElement -> list ModelLink -> ModelFragment ModelElement ModelLink.
  
  Definition instantiateRuleOnPatternA (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    m <- evalGuardExpressionA (RuleA_getGuard r) tr sm sp;
      if m then 
        return optionList2List (map (evalOutputPatternElementExpressionA tr sm sp) (map OutputPatternElementA_getOutputPatternElementExpression (RuleA_getOutputPattern r)))
      else
        None.

  Definition applyOutputPatternReferencesOnPatternA (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (l: list OutputPatternElementReferenceA) (te: TargetModelElement) : list TargetModelLink :=
  optionList2List (map (evalOutputBindingExpressionA tr sm sp te) (map OutputPatternElementReferenceA_getOutputBindingExpression l)).

  Definition applyRuleOnPatternA (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (tes: list TargetModelElement): option (list TargetModelLink) :=
  return (concat (zipWith (applyOutputPatternReferencesOnPatternA tr sm sp) 
                           (map OutputPatternElementA_getOutputPatternElementReferences (RuleA_getOutputPattern r)) tes)).

  Definition maxArityA (tr: TransformationA) : nat :=
    fold_left max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))) 0.
                                                     
  Definition allTuplesA (tr: TransformationA) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArityA tr).

  Fixpoint matchPatternA (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    match l with
    | r :: rs => match evalGuardExpressionA (RuleA_getGuard r) tr sm sp with
                | Some op => Some r
                | None => matchPatternA rs tr sm sp
                end
    | nil => None
    end.
  
  Definition instantiatePatternA (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    r <- matchPatternA l tr sm sp;
     instantiateRuleOnPatternA r tr sm sp.

  Definition applyPatternA (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    r <- matchPatternA l tr sm sp;
      tes <- instantiateRuleOnPatternA r tr sm sp;
        applyRuleOnPatternA r tr sm sp tes.

  Definition transformPatternA (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (ModelFragment TargetModelElement TargetModelLink) :=
      tes <- instantiatePatternA l tr sm sp;
        tls <- applyPatternA l tr sm sp;
  return BuildModelFragment tes tls.

  Definition executeA (tr: TransformationA) (sm : SourceModel) : TargetModel :=
    BuildModel
      (concat (optionList2List (map (instantiatePatternA (TransformationA_getRules tr) tr sm) (allTuplesA tr sm))))
      (concat (optionList2List (map (applyPatternA (TransformationA_getRules tr) tr sm) (allTuplesA tr sm)))). 

  (** * Functions **)

  (** ** list OutputPatternElement **)

  Definition getAllOuputPatternElementElements (l : list OutputPatternElement) : list TargetModelElement :=
    map (getOutputPatternElementTargetModelElement) l.

  Definition getAllOuputPatternElementLinks (l : list OutputPatternElement) : list TargetModelLink :=
    concat (map (getOutputPatternElementTargetModelLinks) l).

  Fixpoint findOutputPatternElementByName (l: list OutputPatternElement) (name: string) : option OutputPatternElement :=
    find (fun oel => beq_string (getOutputPatternElementName oel) name) l.

  
  (** ** Rule application **)

  Fixpoint matchRuleOnPattern (r: Rule) (el: list SourceModelElement) : option (list OutputPatternElement) :=
    match r, el with
    | BuildMultiElementRule t f, e::els =>
      e' <- toModelClass t e;
        matchRuleOnPattern (f e') els
    | BuildSingleElementRule t f, e::nil =>
      e' <- toModelClass t e;
        match (f e') with
        | (true, l) => return l
        | (false, _) => None
        end
    | _, _ => None
    end.
  
  Definition executeRuleOnPattern (r: Rule) (el: list SourceModelElement) : option (list TargetModelElement * list TargetModelLink) :=
    match matchRuleOnPattern r el with
    | Some opel => Some (getAllOuputPatternElementElements opel, getAllOuputPatternElementLinks opel)
    | None => None
    end.

  Definition executeRuleOnPattern' (r: Rule) (el: list SourceModelElement) : option (ModelFragment TargetModelElement TargetModelLink):=
    match matchRuleOnPattern r el with
    | Some opel => Some (BuildModelFragment (getAllOuputPatternElementElements opel) (getAllOuputPatternElementLinks opel))
    | None => None
    end.

  Definition instantiateRuleOnPattern (r: Rule) (inelems: list SourceModelElement) : list TargetModelElement :=
    match executeRuleOnPattern r inelems with
    | Some op => fst op
    | None => nil
    end.

  Definition applyRuleOnPattern (r: Rule) (inelems: list SourceModelElement) : list TargetModelLink :=
    match executeRuleOnPattern r inelems with
    | Some op => snd op
    | None => nil
  end.

  (** ** Resolution **)
  
  Fixpoint resolveFix (tr: list Rule) (name: string) (type: TargetModelClass) (inelems: list SourceModelElement): option (denoteModelClass type) := 
    match tr with
    | r:: rs => match matchRuleOnPattern r inelems with
               | None => resolveFix rs name type inelems
               | Some l => match findOutputPatternElementByName l name with
                          | Some ope => 
                            (getOutputPatternElementElementByType ope type)
                          | None => None
                          end
               end
    | nil => None
    end.

  Definition resolve (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (inelems: list SourceModelElement): option (denoteModelClass type) :=
      resolveFix (tr sm) name type inelems.
    
  Definition resolveAll (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (inelems: list (list SourceModelElement)) : option (list (denoteModelClass type)) :=
    Some (optionList2List (map (resolve tr sm name type) inelems)).
    
  Definition resolveList (tr: list Rule) (name: string) (type: TargetModelClass) (inelems: list (list SourceModelElement)): list (denoteModelClass type) :=
    optionList2List (map (resolveFix tr name type) inelems).

  (** ** Rule matching **)
  
  Fixpoint matchPattern (tr: list Rule) (inelems: list SourceModelElement) : option Rule :=
    match tr with
    | r :: rs => match matchRuleOnPattern r inelems with
                | Some op => Some r
                | None => matchPattern rs inelems
                end
    | nil => None
    end.
  
  Definition instantiatePattern (tr: list Rule) (inelems: list SourceModelElement) : list TargetModelElement :=
    match (matchPattern tr inelems) with
    | Some r => instantiateRuleOnPattern r inelems
    | None => nil
    end.

  Definition applyPattern (tr: list Rule) (inelems: list SourceModelElement) : list TargetModelLink :=
    match (matchPattern tr inelems) with
    | Some r => applyRuleOnPattern r inelems
    | None => nil
    end.

  Definition transformPattern (tr: list Rule) (inelems: list SourceModelElement) : option (list TargetModelElement * list TargetModelLink) :=
    match (matchPattern tr inelems) with
    | Some r => executeRuleOnPattern r inelems
    | None => None
    end.

  (** ** Rule scheduling
  Execution order:

   - execute
     - instantiatePattern 
         matchPattern (recursive on rules)
         instantiateRuleOnPattern
            matchRuleOnPattern (recursive on source pattern)
     - applyPattern
         matchPattern (recursive on rules)
         applyRuleOnPattern
            matchRuleOnPattern (recursive on source pattern)
   **)

  Definition matchPhase (f: Transformation) : Phase := (f (fun c:SourceModel => nil)).

  Definition matched (p: Phase) (m: SourceModel) :=
      p m.

  Definition applyPhase (f: Transformation) : Phase := (f (matchPhase f)).

  Fixpoint arity (tr: Rule) : nat :=
    match tr with
    | BuildMultiElementRule InElType1 x => 1 + (arity (x (bottomModelClass InElType1)))
    | BuildSingleElementRule InElType x => 1
    end.

  Fixpoint maxArity (tr: list Rule) : nat :=
    match tr with
    | r :: rl => (max (arity r) (maxArity rl))
    | _ => 0
    end.

  Definition getRules (tr: Transformation) (sm: SourceModel) : list Rule :=
    matchPhase tr sm.

  Definition getRules' (tr: Transformation) (sm: SourceModel) : list Rule :=
    applyPhase tr sm.

  Definition numberOfRules (tr: Transformation) : nat
    := length ((getRules tr) (BuildModel nil nil)).
    
  Definition allTuples (f: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity (getRules f sm)).

  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    BuildModel
      (concat (map (instantiatePattern (matchPhase tr sm))
                   (allTuples tr sm)))
      (concat (map (applyPattern (applyPhase tr sm))
                   (allTuples tr sm))). 

  (*  Definition allTuples  (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) 10.
  
  Definition execute (tr: Transformation) (sm : SourceModel) : TargetModel :=
    BuildModel
      (concat (map (instantiatePattern (matchPhase tr sm))
                   (allTuples sm)))
      (concat (map (applyPattern (applyPhase tr sm))
                   (allTuples sm))). *)

  (** * Certification **)

  Definition RuleDef : Type := nat * Transformation.

  Fixpoint getRulesFun' (n : nat) (tr: Transformation) : list RuleDef :=
    match n with
        | S x => (cons (n, tr) (getRulesFun' x tr))
        | _ => nil
    end.

  Definition getRule (r : RuleDef) (sm : SourceModel) : option Rule :=
    nth_error (getRules (snd r) sm) (fst r).

  (*
  Definition getRule'''' (n : nat) (sm : SourceModel) : option RuleDef :=
    nth_error (getRules (snd r) sm) (fst r).
  *)

  (* Definition getRuleDef (r : Rule) (tr : Transformation) (sm: SourceModel) : option RuleDef := None. *)
  
  Fixpoint matchPattern'' (tr: list Rule) (inelems: list SourceModelElement) : option nat :=
    match tr with
    | r :: rs => match matchRuleOnPattern r inelems with
                | Some op => Some (length rs)
                | None => matchPattern'' rs inelems
                end
    | nil => None
    end.

  Lemma matchPatternLimit :
    forall (tr: list Rule) (inelems: list SourceModelElement) (n: nat),
      matchPattern'' tr inelems = Some n -> n < length tr.
  Proof.
    intros.
    induction tr.
    * simpl in H. inversion H.
    * simpl in H.
      destruct (matchRuleOnPattern a inelems) eqn:eq1.
      ** inversion H. simpl. omega.
      ** apply IHtr in H. simpl.
         apply lt_trans with (n:=n) (m:=Datatypes.length tr) (p:=S (Datatypes.length tr)) in H.
         exact H. omega.
  Qed.

  (*
  Definition matchPattern' (tr: Transformation) (sp: list SourceModelElement) (sm: SourceModel) : option Rule :=
    matchPattern (getRules tr sm) sp.
  *)

  (*
  Theorem tr_link_surj : 
    forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (tl : TargetModelLink),
      tm = execute tr sm -> In tl (allModelLinks tm) -> 
      (exists (sp : list SourceModelElement) (tls : list TargetModelLink) (r : Rule),
        In r (getRules tr sm) /\
        In tl tls /\
        applyRuleOnPattern r sp = tls /\
        incl sp (allModelElements sm) /\
        incl tls (allModelLinks tm) ).
  Abort.
  *)

  (*
  Theorem tr_object_surj : 
    forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (te : TargetModelElement),
      tm = execute tr sm -> In te (allModelElements tm) -> 
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : Rule),
        In r (getRules tr sm) /\
        In te tp /\
        instantiateRuleOnPattern r sp = tp /\
        incl sp (allModelElements sm) /\
        incl tp (allModelElements tm) /\
        matchPattern (getRules tr sm) sp = Some r ).
  Abort.
  *)

  Lemma matchPattern_in_getRules :
    forall (tr: Transformation) (sm: SourceModel) (r: Rule) (sp: list SourceModelElement),
      (matchPattern (matchPhase tr sm) sp) = Some r -> In r (getRules tr sm).
  Proof.
    unfold getRules.
    intros tr sm.
    induction (matchPhase tr sm).
    - intros. inversion H.
    - intros.
      simpl.
      simpl in H.
      destruct (matchRuleOnPattern a sp) in H.
      -- left. inversion H. reflexivity.
      -- right. apply IHl in H. apply H.
  Qed.

  Theorem tr_surj : 
    forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = execute tr sm -> In t1 (allModelElements tm) -> 
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : Rule),
        In r (getRules tr sm) /\
        In t1 tp /\
        instantiateRuleOnPattern r sp = tp /\
        incl sp (allModelElements sm) /\
        incl tp (allModelElements tm) /\
        matchPattern (getRules tr sm) sp = Some r ).
  Proof.
    intros tr sm tm t1 H0.
    rewrite H0. simpl.
    intros.
    apply concat_map_exists in H. destruct H. destruct H.
    remember (matchPattern (matchPhase tr sm) x) as r'.
    destruct r'.
    
    Focus 2.
    unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction. 
    
    Focus 1.
    exists x, (instantiatePattern (matchPhase tr sm) x),r.
    
    split.
    - apply matchPattern_in_getRules with (sp:=x).
      rewrite Heqr'. reflexivity.
    - split.
      + assumption.
      + split.
        * unfold instantiatePattern.
          rewrite <- Heqr'. reflexivity.
        * split.
          ** unfold allTuples in H.
             apply tuples_up_to_n_incl with (n:=(maxArity (getRules tr sm))).
             assumption.
          ** split.
             *** apply concat_map_incl. assumption.
             *** unfold getRules. symmetry. assumption.
  Qed.

  (*
  Lemma matchPattern_in_getRules' :
    forall (tr: Transformation) (sm: SourceModel) (r: RuleDef) (sp: list SourceModelElement),
      (matchPattern'' (matchPhase tr sm) sp) = Some r -> In r (getRulesFun' (numberOfRules tr) tr).
  Proof.
    unfold getRules.
    intros tr sm.
    induction (matchPhase tr sm).
    - intros. inversion H.
    - intros.
      simpl.
      simpl in H.
      destruct (matchRuleOnPattern a sp) in H.
      -- left. inversion H. reflexivity.
      -- right. apply IHl in H. apply H.
  Qed.
   *)

  (*
  Theorem theorem1 :
    forall (tr: Transformation) (sourcemodel: SourceModel) (targetmodel: TargetModel) (inputel: SourceModelElement),
      In inputel (allModelElements sourcemodel) ->
      targetmodel = execute tr sourcemodel ->
      (matchPattern (matchPhase tr sourcemodel) (inputel::nil)) <> None ->
      incl (instantiatePattern (matchPhase tr sourcemodel) (inputel::nil)) (allModelElements targetmodel). 
  Proof.
    intros.
    rewrite H0.
    unfold execute.
    simpl.
    unfold allTuples.
    apply concat_map_incl.
  Abort.*)

  
  (*  
  Lemma allTuples_in_allModelElements :
    forall (sm:SourceModel) (x: list SourceModelElement),
      In x (allTuples sm) -> incl x (allModelElements sm).
  Proof.
  Abort. 
  *)
  
  (*  
  Theorem tr_distri:
    forall (tr: Transformation)
      (a : SourceModelElement)
      (lse : list SourceModelElement)
      (lsl : list SourceModelLink)
    ,
      (forall (sp: list SourceModelElement),
       (incl sp lse /\ ~ (In a sp)) -> 
       (matchPattern (getRules tr (BuildModel (a :: lse) lsl)) sp) = (matchPattern (getRules tr (BuildModel (lse) lsl)) sp))
      ->    
      (allModelElements (execute tr (BuildModel (a :: lse) lsl))) =
      (execute' tr (BuildModel lse lsl) a)
        ++
        (allModelElements (execute tr (BuildModel lse lsl)))
  .
  Proof.
  Qed. 
  *)

  Instance CoqTLEngine : TransformationEngineTypeClass Transformation RuleDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel :=
    {
      executeFun := execute;
      getRulesFun tr := getRulesFun' (numberOfRules tr) tr;
      instantiateRuleOnPatternFun r sp sm :=
        match (getRule r sm) with
        | Some rule => instantiateRuleOnPattern rule sp
        | None => nil
        end;
      matchPatternFun tr sp sm :=
        match matchPattern'' (getRules tr sm) sp  with
        | Some x => Some ( (numberOfRules tr) - x - 1 , tr )
        | None => None
        end;
      allSourceModelElements:= allModelElements;
      allTargetModelElements:= allModelElements;        
    }.
  Proof.
    Focus 3.
    intros.
    remember (matchPattern'' (getRules tr sm) sp) as m.
    induction m.
    inversion H.
    Focus 1.
    symmetry in Heqm.
    apply matchPatternLimit in Heqm.
    
    
    
  (*intros.
  apply tr_surj  with (t1:=t1) in H.
  destruct H as [sp].
  destruct H as [tp].
  destruct H as [r].
  destruct H.
  destruct H1.
  destruct H2.
  destruct H3.
  destruct H4.
  exists sp, tp.
  + exsits 
  + auto. *)
  
  (*intros tr sm tm t1 H0.
    rewrite H0. simpl.
    intros.
    apply concat_map_exists in H. destruct H. destruct H.
    remember (matchPattern'' (matchPhase tr sm) x) as r'.
    destruct r'.
    remember (n, tr) as r.
    
    Focus 1.
    exists x, (instantiatePattern (matchPhase tr sm) x), r.
    
    split.
    - apply matchPattern_in_getRules' with (sp:=x).
      rewrite Heqr'. reflexivity.
    - split.
      + assumption.
      + split.
        * unfold instantiatePattern.
          rewrite <- Heqr'. reflexivity.
        * split.
          ** unfold allTuples in H.
             apply tuples_up_to_n_incl with (n:=(maxArity (getRules tr sm))).
             assumption.
          ** split.
             *** apply concat_map_incl. assumption.
             *** unfold getRules. symmetry. assumption.

    
    Focus 2.
    unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction. *)
  Abort.
  
End CoqTL.

(* Set Implicit Arguments Inference *)

Arguments Phase : default implicits.
Arguments BuildSingleElementRule : default implicits.
Arguments BuildMultiElementRule : default implicits.
Arguments BuildOutputPatternElement : default implicits.
Arguments BuildOutputPatternElementReference : default implicits.
Arguments resolve : default implicits.
Arguments execute : default implicits.
Arguments getOutputPatternElementTargetModelElement : default implicits.
Arguments matchPhase : default implicits.
