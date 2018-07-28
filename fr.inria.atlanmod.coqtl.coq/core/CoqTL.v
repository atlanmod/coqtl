Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.


Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.tTop.


Set Implicit Arguments.

Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.
  
  About SourceModel.

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
    match o with BuildOutputPatternElementReference type link => type end.
                                                                                       
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
    match o with BuildOutputPatternElement type name el refs => name end.

  Definition getOutputPatternElementType (o :  OutputPatternElement) : TargetModelClass :=
    match o with BuildOutputPatternElement type name el refs => type end.

  Definition getOutputPatternElementBindings (o :  OutputPatternElement) : ((denoteModelClass (getOutputPatternElementType o)) -> list OutputPatternElementReference) :=
    match o with BuildOutputPatternElement type name el refs => refs end.

  Definition getOutputPatternElementElementType (o :  OutputPatternElement) : Set :=
    match o with BuildOutputPatternElement type name el refs => denoteModelClass type end.

  Definition getOutputPatternElementElement (o :  OutputPatternElement) : getOutputPatternElementElementType o :=
    match o with BuildOutputPatternElement type name el refs => el end.
  
  Definition getOutputPatternElementTargetModelElement (o :  OutputPatternElement) : TargetModelElement :=
    match o with BuildOutputPatternElement OutElType x x0 x1 => toModelElement OutElType x0 end.

  Definition getOutputPatternElementTargetModelLinks (o :  OutputPatternElement): list TargetModelLink :=
    match o with BuildOutputPatternElement type name el refs => getOutputPatternElementReferenceTargetModelLinks (refs el) end.

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
      (mapWithIndex (parseRule tr) 0 (tr (fun c:SourceModel => nil) (Build_Model nil nil) )) tr.

  Definition parsePhase (tr: Phase) : TransformationA :=
    parseTransformation (fun t: Phase => tr).

  (** * Expression Evaluation **)

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputBindingExpressionFix (o : OutputBindingExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) (te: TargetModelElement) : option TargetModelLink :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputBindingExpressionFix o (f e') ts sm els te
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputBindingExpressionA_getOutputPatternElement o));
        te' <- toModelClass (getOutputPatternElementType ope) te;
        oper <- (nth_error ((getOutputPatternElementBindings ope) te') (OutputBindingExpressionA_getOutputBinding o));
        (OutputPatternElementReferenceLink oper)
    | _, _, _ => None
    end.
  
  Definition evalOutputBindingExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (te: TargetModelElement) (o : OutputBindingExpressionA) : option (TargetModelLink) :=
  r <- (nth_error ((TransformationA_getTransformation tr) ((TransformationA_getTransformation tr) (fun c:SourceModel => nil)) sm) (OutputBindingExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputBindingExpressionA_getRule o));
  evalOutputBindingExpressionFix o r (RuleA_getInTypes ra) sm sp te. 

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalOutputPatternElementExpressionFix (o : OutputPatternElementExpressionA) (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option TargetModelElement :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalOutputPatternElementExpressionFix o (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
        ope <- (nth_error (snd (f e')) (OutputPatternElementExpressionA_getOutputPatternElement o));
        return (getOutputPatternElementTargetModelElement ope)
    | _, _, _ => None
    end.
  
  Definition evalOutputPatternElementExpression (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (o : OutputPatternElementExpressionA): option TargetModelElement :=
  r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (OutputPatternElementExpressionA_getRule o));
    ra <- (nth_error (TransformationA_getRules tr) (OutputPatternElementExpressionA_getRule o));
  evalOutputPatternElementExpressionFix o r (RuleA_getInTypes ra) sm sp. 


  (* Before evaluate guard, pre-check the intypes of rule and source elems length are equal. immediate stop eval if not. *)
  Definition evalGuardExpressionPre (r: RuleA) (sp: list SourceModelElement) : option bool :=
    let lenInTypes := (length (RuleA_getInTypes r)) in
      let lenSp := (length sp) in
        match beq_nat lenInTypes lenSp with
         | true => Some true 
         | false => None
        end.

  (* the expression is checked against the types in the concrete transformation, may cause problems in theorems *)
  Fixpoint evalGuardExpressionFix (r : Rule) (intypes: list SourceModelClass) (sm: SourceModel) (el: list SourceModelElement) : option bool :=
    match r, intypes, el with
    | BuildMultiElementRule s f, t::ts, e::els =>
      e' <- toModelClass s e;
        evalGuardExpressionFix (f e') ts sm els
    | BuildSingleElementRule s f, t::nil, e::nil =>
      e' <- toModelClass s e;
      return (fst (f e'))
    | _, _, _ => None
    end.

  Definition evalGuardExpression (o : GuardExpressionA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option bool :=
    r <- (nth_error ((TransformationA_getTransformation tr) (fun c:SourceModel => nil) sm) (GuardExpressionA_getRule o));
      ra <- (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule o));
          evalGuardExpressionFix r (RuleA_getInTypes ra) sm sp. 

  (** * Engine **)

  (** ** Rule application **)

  Inductive ModelFragment (ModelElement: Type) (ModelLink: Type): Type :=
    BuildModelFragment: list ModelElement -> list ModelLink -> ModelFragment ModelElement ModelLink.
  
  Definition instantiateRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    pre <- evalGuardExpressionPre r sp;
    m <- evalGuardExpression (RuleA_getGuard r) tr sm sp;
      if m then 
        return optionList2List (map (evalOutputPatternElementExpression tr sm sp) (map OutputPatternElementA_getOutputPatternElementExpression (RuleA_getOutputPattern r)))
      else
        None.

  Definition applyOutputPatternReferencesOnPattern (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (l: list OutputPatternElementReferenceA) (te: TargetModelElement) : list TargetModelLink :=
  optionList2List (map (evalOutputBindingExpression tr sm sp te) (map OutputPatternElementReferenceA_getOutputBindingExpression l)).

  Definition applyRuleOnPattern (r: RuleA) (tr: TransformationA) (sm: SourceModel) (sp: list SourceModelElement) (tes: list TargetModelElement): option (list TargetModelLink) :=
  return (concat (zipWith (applyOutputPatternReferencesOnPattern tr sm sp) 
                          (map OutputPatternElementA_getOutputPatternElementReferences (RuleA_getOutputPattern r)) tes)).

  (** ** Rule matching **)
  Definition matchRuleOnPattern (r: RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option bool :=
    evalGuardExpression (RuleA_getGuard r) tr sm sp.

  Fixpoint matchPatternFix (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    match l with
    | r :: rs => match evalGuardExpression (RuleA_getGuard r) tr sm sp with
                | Some false => matchPatternFix rs tr sm sp
                | Some op => Some r
                | None => matchPatternFix rs tr sm sp
                end
    | nil => None
    end.

  Definition matchPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    matchPatternFix (TransformationA_getRules tr) tr sm sp.
  
  Definition instantiatePattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelElement) :=
    r <- matchPattern tr sm sp;
     instantiateRuleOnPattern r tr sm sp.

  Definition applyPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (list TargetModelLink) :=
    r <- matchPattern tr sm sp;
      tes <- instantiateRuleOnPattern r tr sm sp;
        applyRuleOnPattern r tr sm sp tes.

  Definition transformPattern (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option (ModelFragment TargetModelElement TargetModelLink) :=
      tes <- instantiatePattern tr sm sp;
        tls <- applyPattern tr sm sp;
  return BuildModelFragment tes tls.

  (** ** Resolution **)

  Definition resolveFix (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement) : option (denoteModelClass type) :=
    r <- matchPattern tr sm sp;
      ope <- find (fun oel => beq_string (OutputPatternElementA_getName oel) name) (RuleA_getOutputPattern r);
      te <- evalOutputPatternElementExpression tr sm sp (OutputPatternElementA_getOutputPatternElementExpression ope);
      toModelClass type te.

  Definition resolve (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sp: list SourceModelElement): option (denoteModelClass type) :=
    resolveFix (TransformationA_getRules (parsePhase tr)) (parsePhase tr) sm name type sp.
    
  Definition resolveAll (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (sps: list (list SourceModelElement)) : option (list (denoteModelClass type)) :=
    Some (optionList2List (map (resolve tr sm name type) sps)).

  (** ** Rule scheduling **)
  
  Fixpoint max (l : list nat) : nat :=
    match l with nil => 0
    | a::nil => a
    | a::m => let b:= max m in if ble_nat a b then b else a
    end.
    
  Definition maxArity (tr: TransformationA) : nat :=
    max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))).

  (* Fold-left alternative
     
     Definition maxArity (tr: TransformationA) : nat :=
     fold_left max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))) 0. *)
                                                     
  Definition allTuples (tr: TransformationA) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (allModelElements sm) (maxArity tr).
  
  Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))).

  (* One-phase alternative

     Definition pairconcat 
  
     Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
     let res := (pairconcat (map (transformPattern tr sm) (allTuples tr sm))) in
     Build_Model
      (fst res) (snd res).*)
  
  (** * Typeclass instantiation **)
  
  Theorem match_incl :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleA),
          matchPattern tr sm sp = Some r -> In r (TransformationA_getRules tr).
  Proof.
    unfold matchPattern.
    intro tr.
    induction (TransformationA_getRules tr).
    - intros. inversion H.
    - simpl.
      intros sm sp r.
      destruct (evalGuardExpression (RuleA_getGuard a) tr sm sp).
      * intros.
        destruct b.
        ** left.
           inversion H. 
           auto.
        ** right.
           apply IHl with sm sp.
           auto.
      * intros.
        apply IHl in H.
        right.
        assumption.
  Qed.

  Theorem tr_instantiate_pattern_derivable : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
           (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleA),
      tm = execute tr sm ->
      instantiateRuleOnPattern r tr sm sp = Some tp ->
      matchPattern tr sm sp = Some r ->
      instantiatePattern tr sm sp = Some tp.
  Proof.
    intros.
    unfold instantiatePattern.
    rewrite H1.
    assumption.
  Qed.

  Theorem tr_apply_pattern_derivable : 
        forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
               (sp : list SourceModelElement) (tp : list TargetModelElement) (tls : list  TargetModelLink) (r : RuleA),
          tm = execute tr sm ->
          applyRuleOnPattern r tr sm sp tp = Some tls ->
          instantiateRuleOnPattern r tr sm sp = Some tp ->
          matchPattern tr sm sp = Some r ->
          applyPattern tr sm sp = Some tls.
  Proof.
    intros.
    unfold applyPattern.
    rewrite H2.
    rewrite H1.
    assumption.
  Qed.

     
  Theorem tr_surj_elements : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = execute tr sm -> In t1 (allModelElements tm) -> 
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleA),
        In r (TransformationA_getRules tr) /\
        In t1 tp /\
        instantiateRuleOnPattern r tr sm sp = Some tp /\
        incl sp (allModelElements sm) /\
        incl tp (allModelElements tm) /\
        matchPattern tr sm sp = Some r ).
  Proof.
    intros tr sm tm t1 H0.
    rewrite H0. simpl.
    intros.
    apply concat_map_option_exists in H.
    destruct H. destruct H.
    rename x into sp1.
    remember (matchPattern tr sm sp1) as r'.
    destruct r'.
    
    Focus 2.
    unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction.
    
    Focus 1.
    remember (instantiatePattern tr sm sp1) as tp_temp.
    destruct tp_temp eqn:tp1_case.
     Focus 2.
     contradiction.
     
     Focus 1.
     rename l into tp1.
     exists sp1, tp1, r.
     repeat split.
      - apply match_incl with (sp:=sp1) (sm:=sm).
         rewrite Heqr'. reflexivity.
      - assumption.
      - symmetry. unfold instantiatePattern in Heqtp_temp. rewrite <- Heqr' in Heqtp_temp. assumption.
      - apply tuples_up_to_n_incl with (n:=(maxArity tr)).
         assumption.
      - apply concat_map_option_incl with (a:=sp1). assumption. symmetry. assumption.
      - symmetry. assumption.
   Qed.

(* 
   Theorem tr_surj_links : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
      tm = execute tr sm -> In t1 (allModelLinks tm) -> 
      (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : RuleA),
        In r (TransformationA_getRules tr) /\
        In t1 tpl /\
        applyRuleOnPattern r tr sm sp tel = Some tpl /\
        incl sp (allModelElements sm) /\
        incl tpl (allModelLinks tm) /\
        matchPattern tr sm sp = Some r ).
  Proof.
    intros tr sm tm t1 H0.
    rewrite H0. simpl.
    intros.
    apply concat_map_option_exists in H.
    destruct H. destruct H.
    rename x into sp1.
    remember (applyPattern tr sm sp1) as r'.
    destruct r'.
      Focus 2.
      contradiction.
    
      Focus 1.
      unfold applyPattern in Heqr'.
      destruct (matchPattern tr sm sp1) eqn:Hmatch. 
        Focus 2.
        inversion Heqr'.

        Focus 1.
        destruct (instantiateRuleOnPattern r tr sm sp1) eqn:Hinst.
          Focus 2.
          inversion Heqr'.

          Focus 1.
          rename l0 into te1.
          rename l into tpl.
          exists sp1, te1, tpl, r. 
          repeat split.
          --- apply match_incl with (sp:=sp1) (sm:=sm).
              assumption.
          --- assumption.
          --- symmetry. assumption.
          --- apply tuples_up_to_n_incl with (n:=(maxArity tr)).
             assumption.
          --- apply concat_map_option_incl with (a:=sp1). 
               ---- assumption. 
               ---- unfold applyPattern. rewrite Hmatch. rewrite Hinst. symmetry. assumption.
          --- assumption.
  Qed.

  Lemma MaxArity_geq_lenOfrule :
        forall (tr: TransformationA) (r: RuleA),
          In r (TransformationA_getRules tr) -> 
          maxArity tr >= length (RuleA_getInTypes r).
  Proof.
    intros.
    destruct tr.
    simpl in H.
    rename l into rules.
    induction rules.
    - contradiction.
    - simpl in H.
      destruct H.
      + unfold maxArity.
        unfold TransformationA_getRules.
        rewrite H.
        simpl. 
        destruct ((map (Datatypes.length (A:=SourceModelClass)) (map RuleA_getInTypes rules))).
        ++ simpl. omega.
        ++ destruct (ble_nat (Datatypes.length (RuleA_getInTypes r)) (max (n :: l))) eqn:max.
           +++ apply ble_nat_true. assumption.
           +++ omega.
      + apply IHrules in H.
        assert (maxArity (BuildTransformationA (a :: rules) t) >= maxArity (BuildTransformationA rules t)).
        { 
          unfold maxArity.
          unfold TransformationA_getRules.
          simpl. 
          destruct (map (Datatypes.length (A:=SourceModelClass)) (map RuleA_getInTypes rules)) eqn: rules_ca.
          ++ simpl. omega.
          ++ destruct (ble_nat (Datatypes.length (RuleA_getInTypes a)) (max (n :: l))) eqn:max.
             +++ omega.
             +++ apply ble_nat_false in max.
                 omega.
        }
        remember (maxArity (BuildTransformationA (a :: rules) t)) as x.
        remember (maxArity (BuildTransformationA rules t)) as y.
        remember (Datatypes.length (RuleA_getInTypes r)) as z.
        apply (@ge_trans x y z); assumption.
  Qed.

  Lemma eq_ruletype_sp :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
          incl sp (allModelElements sm) ->
          instantiateRuleOnPattern r tr sm sp = Some tp -> length (RuleA_getInTypes r) = Datatypes.length sp.
  Proof.
    intros.
    unfold instantiateRuleOnPattern in H0.
    destruct (evalGuardExpressionPre r sp) eqn: guard; inversion H0.
    unfold evalGuardExpressionPre in guard.
    destruct (Datatypes.length (RuleA_getInTypes r) =? Datatypes.length sp) eqn: ca.
    - apply  beq_nat_true in ca. assumption.
    - inversion guard.
  Qed.

  Lemma InstantiatePattern_le_maxArity :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
      incl sp (allModelElements sm) ->
      In r (TransformationA_getRules tr) ->
      instantiateRuleOnPattern r tr sm sp= Some tp -> maxArity tr >= Datatypes.length sp.
  Proof.
    intros.
    assert (length (RuleA_getInTypes r) = Datatypes.length sp). { apply (@eq_ruletype_sp tr sm sp tp r); assumption. }
                                                                assert ( maxArity tr >= length (RuleA_getInTypes r)). { apply (@MaxArity_geq_lenOfrule). assumption. }
                                                                                                                     rewrite H2 in H3.
    assumption.
  Qed.

  Lemma In_allTuples :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
      incl sp (allModelElements sm) ->
      In r (TransformationA_getRules tr) ->
      instantiateRuleOnPattern r tr sm sp = Some tp -> In sp (allTuples tr sm).
  Proof.
    intros.
    case (le_lt_dec (length sp) (maxArity tr)).
    - intros.
      unfold allTuples.
      apply tuples_up_to_n_incl_length.
      + assumption.
      + assumption.
    - intros.
      assert (maxArity tr >= Datatypes.length sp). { apply (@InstantiatePattern_le_maxArity tr sm sp tp r); assumption. }
        omega.
  Qed.

  Theorem outp_incl_elements :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
      (sp : list SourceModelElement) (r: RuleA) (tes: list TargetModelElement),
      tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (allModelElements sm) ->
      matchPattern tr sm sp = Some r ->
      instantiateRuleOnPattern r tr sm sp = Some tes ->
      incl tes (allModelElements tm).
  Proof.
    intros.
    rewrite H.
    simpl.
    apply concat_map_option_incl with (a:=sp).
    - apply In_allTuples with (tp:=tes) (r:=r); assumption.
    - unfold instantiatePattern.
      rewrite H2.
      assumption.
  Qed.

  Theorem outp_incl_links :
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
      (sp : list SourceModelElement) (r: RuleA) (tes: list TargetModelElement) (tls: list TargetModelLink),
      tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (allModelElements sm) ->
      matchPattern tr sm sp = Some r ->
      instantiateRuleOnPattern r tr sm sp = Some tes ->
      applyRuleOnPattern r tr sm sp tes = Some tls ->
      incl tls (allModelLinks tm).
  Proof.
    intros.
    rewrite H.
    simpl.
    apply concat_map_option_incl with (a:=sp).
    - apply In_allTuples with (tp:=tes) (r:=r); assumption.
    - unfold applyPattern.
      rewrite H2.
      rewrite H3.
      assumption.
  Qed.

  Theorem match_functional :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleA) (r2: RuleA),
      matchPattern tr sm sp = Some r1 -> 
      matchPattern tr sm sp = Some r2 -> 
      r1 = r2.
  Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
  Qed.

  Instance CoqTLEngine : 
    TransformationEngine TransformationA RuleA OutputPatternElementA OutputPatternElementReferenceA SourceModelElement SourceModelLink TargetModelElement TargetModelLink := 
    {
      getRules := TransformationA_getRules;
      getOutputPatternElements := RuleA_getOutputPattern;
      getOutputPatternElementReferences := OutputPatternElementA_getOutputPatternElementReferences;

      execute := execute;
      
      matchPattern := matchPattern;
      instantiatePattern := instantiatePattern;
      applyPattern := applyPattern;

      matchRuleOnPattern := matchRuleOnPattern;
      instantiateRuleOnPattern := instantiateRuleOnPattern;
      applyRuleOnPattern := applyRuleOnPattern;

      instantiate_pattern_derivable :=  tr_instantiate_pattern_derivable;
      apply_pattern_derivable :=  tr_apply_pattern_derivable; 
      tr_surj_elements := tr_surj_elements;
      tr_surj_links := tr_surj_links;

      outp_incl_elements := outp_incl_elements;
      outp_incl_links := outp_incl_links;
      match_in := match_incl;
      match_functional := match_functional;
    }.
  
End CoqTL.

*)

(* Set Implicit Arguments Inference *)

Arguments Phase : default implicits.
Arguments BuildSingleElementRule : default implicits.
Arguments BuildMultiElementRule : default implicits.
Arguments BuildOutputPatternElement : default implicits.
Arguments BuildOutputPatternElementReference : default implicits.
Arguments resolve : default implicits.
Arguments execute : default implicits.
Arguments getOutputPatternElementTargetModelElement : default implicits.
