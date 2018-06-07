Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import ZArith.

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

  Fixpoint matchPatternFix (l: list RuleA) (tr: TransformationA) (sm : SourceModel) (sp: list SourceModelElement) : option RuleA :=
    match l with
    | r :: rs => match evalGuardExpression (RuleA_getGuard r) tr sm sp with
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
  Fixpoint ble_nat (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => ble_nat n' m'
      end
  end.
  
  Fixpoint max (l : list nat) : nat :=
    match l with nil => 0
    | a::nil => a
    | a::m => let b:= max m in if ble_nat a b then b else a
    end.

  (* Definition maxArity (tr: TransformationA) : nat :=
    fold_left max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))) 0. *)
    
  Definition maxArity (tr: TransformationA) : nat :=
    max (map (length (A:=SourceModelClass)) (map RuleA_getInTypes (TransformationA_getRules tr))).
                                                     
  Definition allTuples (tr: TransformationA) (sm : SourceModel) :list (list SourceModelElement) :=
    tuples_up_to_n (@allModelElements _ _ sm) (maxArity tr).

  Definition execute (tr: TransformationA) (sm : SourceModel) : TargetModel :=
    Build_Model
      (concat (optionList2List (map (instantiatePattern tr sm) (allTuples tr sm))))
      (concat (optionList2List (map (applyPattern tr sm) (allTuples tr sm)))). 

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
        inversion H.
        left.
        reflexivity.
      * intros.
        apply IHl in H.
        right.
        assumption.
  Qed.



 Theorem tr_instantiate_pattern_derivable : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) 
           (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleA),
      tm = execute tr sm -> incl tp (@allModelElements _ _ tm) ->
      instantiateRuleOnPattern r tr sm sp = Some tp ->
      matchPattern tr sm sp = Some r ->
      instantiatePattern tr sm sp = Some tp.
 Proof.
   intros.
   unfold instantiatePattern.
   rewrite H2.
   assumption.
 Qed.
 
      
 Theorem tr_surj_elements : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
      tm = execute tr sm -> In t1 (@allModelElements _ _ tm) -> 
      (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleA),
        In r (TransformationA_getRules tr) /\
        In t1 tp /\
        instantiateRuleOnPattern r tr sm sp = Some tp /\
        incl sp (@allModelElements _ _ sm) /\
        incl tp (@allModelElements _ _ tm) /\
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

 Theorem tr_surj_links : 
    forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
      tm = execute tr sm -> In t1 (@allModelLinks _ _ tm) -> 
      (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : RuleA),
        In r (TransformationA_getRules tr) /\
        In t1 tpl /\
        applyRuleOnPattern r tr sm sp tel = Some tpl /\
        incl sp (@allModelElements _ _ sm) /\
        incl tpl (@allModelLinks _ _ tm) /\
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

Lemma ge_trans : forall a b c,
  a >= b -> b >= c -> a >= c.
Proof.
  intuition.
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros. induction n.
  apply le_n.
  apply le_S. apply IHn.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros. induction H.
  apply le_n.
  apply le_S. apply IHle.
Qed.

Locate le_n.
Lemma ble_nat_true : forall n m,
    ble_nat n m = true -> n <= m.
Proof.
  intros n m. generalize dependent n. induction m.
  - destruct n.
    -- intros. apply le_n.
    -- simpl. intros. inversion H.
  - intros. destruct n.
    -- apply O_le_n.
    -- apply n_le_m__Sn_le_Sm. apply IHm.
                 simpl in H. apply H.
Qed.


Lemma ble_nat_false : forall n m,
    ble_nat n m = false -> n > m.
Proof.
induction n; intros.
- inversion H.
- destruct m.
  -- auto with arith.
  -- apply lt_n_S.
     apply IHn.
     simpl in H.
     assumption.
Qed.


Theorem MaxArity_geq_lenOfrule :
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

Theorem eq_ruletype_sp :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
          incl sp (@allModelElements _ _ sm) ->
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




Theorem InstantiatePattern_le_maxArity :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement) (r: RuleA),
          incl sp (@allModelElements _ _ sm) ->
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
          incl sp (@allModelElements _ _ sm) ->
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
          tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (@allModelElements _ _ sm) ->
          matchPattern tr sm sp = Some r ->
          instantiateRuleOnPattern r tr sm sp = Some tes ->
          incl tes (@allModelElements _ _ tm).
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
          tm = execute tr sm -> In r (TransformationA_getRules tr) -> incl sp (@allModelElements _ _ sm) ->
          matchPattern tr sm sp = Some r ->
          instantiateRuleOnPattern r tr sm sp = Some tes ->
          applyRuleOnPattern r tr sm sp tes = Some tls ->
          incl tls (@allModelLinks _ _ tm).
Proof.
Abort.

Instance CoqTLEngine : 
  TransformationEngineTypeClass TransformationA RuleA OutputPatternElementA OutputPatternElementReferenceA
  SourceModelElement SourceModelLink SourceModel
  TargetModelElement TargetModelLink TargetModel := 
  {
    allSourceModelElements := (@allModelElements SourceModelElement SourceModelLink);
    allSourceModelLinks := (@allModelLinks SourceModelElement SourceModelLink);
    allTargetModelElements := (@allModelElements TargetModelElement TargetModelLink);
    allTargetModelLinks := (@allModelLinks TargetModelElement TargetModelLink);

    getRulesFun := TransformationA_getRules;
    getOutputPatternElementsFun := RuleA_getOutputPattern;
    getOutputPatternElementReferencesFun := OutputPatternElementA_getOutputPatternElementReferences;

    executeFun := execute;
    
    matchPatternFun := matchPattern;
    instantiatePatternFun := instantiatePattern;
    applyPatternFun := applyPattern;

(*     matchRuleOnPatternFun := *)
    instantiateRuleOnPatternFun := instantiateRuleOnPattern;
    applyRuleOnPatternFun := applyRuleOnPattern;

    tr_instantiate_pattern_derivable :=  tr_instantiate_pattern_derivable; 
    tr_surj_elements := tr_surj_elements;
    tr_surj_links := tr_surj_links;

    outp_incl_elements := outp_incl_elements;
    match_in := match_incl;
  }.
Proof.  
Abort.

(*Theorem evalGuardExpression_patternLength :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleA),
      length sp > length (RuleA_getInTypes r) -> In r (TransformationA_getRules tr) -> not (evalGuardExpression (RuleA_getGuard r) tr sm sp = Some true).
Proof.
  intros.
  unfold evalGuardExpression.
  destruct (nth_error (TransformationA_getTransformation tr (fun _ : SourceModel => nil) sm)
                      (GuardExpressionA_getRule (RuleA_getGuard r))) eqn:eqr.
  - destruct (nth_error (TransformationA_getRules tr) (GuardExpressionA_getRule (RuleA_getGuard r))) eqn:eqra.
    + induction (RuleA_getInTypes r1).
      ++ unfold evalGuardExpressionFix.
         destruct r0 eqn:eqr0.
         +++ unfold not. intros. inversion H1.
         +++ unfold not. intros. inversion H1.
      ++ *)
  
(* Theorem matchPattern_maxArity :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleA),
      length sp > maxArity tr -> In r (TransformationA_getRules tr) -> evalGuardExpression (RuleA_getGuard r) tr sm sp = Some false.
 Proof.
   intros.
   unfold evalGuardExpression.
   induction sp.
   - inversion H.
   - destruct (le_dec (Datatypes.length sp) (maxArity tr)). *)
  
(* Theorem matchPattern_maxArity :
    forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement),
      length sp > maxArity tr -> 
      matchPattern tr sm sp = None.
  Proof.
    unfold matchPattern.
    intros tr.
    induction (TransformationA_getRules tr).
    - reflexivity.
    - intros.
      simpl.
      destruct (evalGuardExpression (RuleA_getGuard a) tr sm sp) eqn:guard.
      Focus 2.
      apply IHl.
      apply H.
      Focus 1. *)

(*Theorem In_allTuples :
        forall (tr: TransformationA) (sm : SourceModel) (sp : list SourceModelElement) (tp : list TargetModelElement),
          incl sp (@allModelElements _ _ sm) ->
          instantiatePattern tr sm sp = Some tp -> In sp (allTuples tr sm).
  Proof.
    intros.
    case (le_lt_dec (length sp) (maxArity tr)).
    - intros.
      unfold allTuples.
      apply tuples_up_to_n_incl_length.
      + assumption.
      + assumption.
    - intros. *)

  (* Theorem outp_incl :
        forall (tr: TransformationA) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (tp : list TargetModelElement),
          tm = execute tr sm -> incl sp (allModelElements sm) ->
          instantiatePattern (TransformationA_getRules tr) tr sm sp = Some tp -> incl tp (allModelElements tm).
  Proof.
    intros.
    unfold execute in H.
    rewrite H. simpl.
    apply concat_incl with (b:=optionListToList (instantiatePattern (TransformationA_getRules tr) tr sm sp)).
    - rewrite H1. simpl. apply incl_refl.
    - rewrite H1. simpl.
      apply optionList2List_In_inv.
      rewrite <- H1.
      apply in_map.
      
  Abort. *)
 
(* Lemma matchPatternLimit :
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
  Qed.*)

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

  (* Theorem tr_surj : 
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
  Qed. *)

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

  (* Instance CoqTLEngine : TransformationEngineTypeClass Transformation RuleDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel :=
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
    apply matchPatternLimit in Heqm. *)
    
    
    
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
    unfold instantiatePattern in H1. rewrite <- Heqr' in H1. contradiction.
  Abort.  *)
  
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
