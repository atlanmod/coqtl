Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.

Set Implicit Arguments.

(* Type Class of Model *)

Class Metamodel (ModelElement: Type) (ModelLink: Type) (ModelClass: Type) (ModelReference: Type) :=
  {
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


(* Each model is constructed by a list of 
   {@code ModelElement} and {@ModelLink}. *)

Inductive Model (ModelElement: Type) (ModelLink: Type): Type :=
  BuildModel: list ModelElement -> list ModelLink -> Model ModelElement ModelLink.

Definition allModelElements {ModelElement: Type} {ModelLink: Type} (m : Model ModelElement ModelLink) : list ModelElement :=
  match m with BuildModel l _ => l end.

Definition allModelLinks {ModelElement: Type} {ModelLink: Type} (m : Model ModelElement ModelLink) : list ModelLink :=
  match m with BuildModel _ l => l end.


(* Define CoqTL, a Transformation Interpreter *)

(* TODO: Encode as a type class? *)
Section CoqTL.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).
  
  Definition SourceModel := Model SourceModelElement SourceModelLink.
  Definition TargetModel := Model TargetModelElement TargetModelLink.
  
  (* Abstract Syntax *)

  (* Example: 
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
   *)


  (* Build OutputPatternElementReference with :
      an ref_type
      an trg_instance
      and a ref_ends         
   *)
  Inductive OutputPatternElementReference : Type :=
  | BuildOutputPatternElementReference : forall (OutRefs: TargetModelReference),
      (option (denoteModelReference OutRefs))
      -> OutputPatternElementReference.

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

  Inductive Rule: Type :=
  | BuildMultiElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> Rule)
        -> Rule
  | BuildSingleElementRule :
      forall (InElType: SourceModelClass),
        ((denoteModelClass InElType) -> (bool * list OutputPatternElement))
        -> Rule.

  Definition Phase : Type := SourceModel -> (list Rule).

  Definition Transformation : Type := Phase -> Phase.  
  
  (* Engine *)

  Definition getOutputPatternElementName (o :  OutputPatternElement) : string :=
    match o with
      (BuildOutputPatternElement type name el refs) => name
    end.

  Definition getOutputPatternElementType (o :  OutputPatternElement) : TargetModelClass :=
    match o with
      (BuildOutputPatternElement type name el refs) => type
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

  Definition getAllOuputPatternElementElements (l : list OutputPatternElement) : list TargetModelElement :=
    map (getOutputPatternElementTargetModelElement) l.

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

  Definition getOutputPatternElementTargetModelLinks (o :  OutputPatternElement): list TargetModelLink :=
    match o with
      (BuildOutputPatternElement type name el refs) => getOutputPatternElementReferenceTargetModelLinks (refs el)
    end.

  Definition getAllOuputPatternElementLinks (l : list OutputPatternElement) : list TargetModelLink :=
    concat (map (getOutputPatternElementTargetModelLinks) l).

  Fixpoint findOutputPatternElementByName (l: list OutputPatternElement) (name: string) : option OutputPatternElement :=
    find (fun oel => beq_string (getOutputPatternElementName oel) name) l.

  Definition getOutputPatternElementElementByType (o :  OutputPatternElement) (type:TargetModelClass) : option (denoteModelClass type).
  Proof.
    remember o as ope.
    destruct o.
    remember (eqModelClass_dec type OutElType) as equal.
    destruct equal.
    - rewrite e.
      exact (Some d).
    - exact None.
  Defined.

  (* 
   Return 
   
   @param r 
   @param el
   @return a list of {@OutputPatternElement}
   *)
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

  (* Execution order 

   * execute
     * instantiatePattern 
         matchPattern (recursive on rules)
         instantiateRuleOnPattern
            matchRuleOnPattern (recursive on source pattern)
     * applyPattern
         matchPattern (recursive on rules)
         applyRuleOnPattern
            matchRuleOnPattern (recursive on source pattern)
   *)
  
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

    Definition SourceMetamodel_toEObject (c : SourceModelElement) : SourceModelElement := c.
  
    Definition singletons (l : list SourceModelElement) : list (list SourceModelElement) :=
        listToListList l.
    
    Definition resolveAll (tr: Phase) (sm:SourceModel) (name: string) (type: TargetModelClass) (inelems: list (list SourceModelElement)) : option (list (denoteModelClass type)) :=
    Some (optionList2List (map (resolve tr sm name type) inelems)).
    
  Definition resolveList (tr: list Rule) (name: string) (type: TargetModelClass) (inelems: list (list SourceModelElement)): list (denoteModelClass type) :=
    optionList2List (map (resolveFix tr name type) inelems).

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

  (* TODO: Rules are actually "applied Rules"*)
  Definition getRules (tr: Transformation) (sm: SourceModel) : list Rule :=
    matchPhase tr sm.

  Definition getRules' (tr: Transformation) (sm: SourceModel) : list Rule :=
    applyPhase tr sm.
    
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

Class TransformationEngineTypeClass (TransformationDef: Type) (SourceModel: Type) (TargetModel: Type) (RuleDef: Type) :=
  {
    (*executeFun: TransformationDef -> SourceModel -> TargetModel; *)
    (*allModelElements: Model ModelElement ModelLink -> list ModelElement;*)
    getRulesFun: TransformationDef -> list RuleDef;
    (*instantiateRuleOnPatternFun: RuleDef -> list SourceModelElement -> list TargetModelElement; TODO: to fix *)
    (*matchPatternFun: list RuleDef -> list SourceModelElement -> option RuleDef;  TODO: to fix *)
  }. 

Theorem tr_surj' : 
  forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
    tm = execute tr sm -> In t1 (allModelElements tm) -> 
    (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : Rule),
        In r (getRules tr sm) /\
        In t1 tp /\
        instantiateRuleOnPattern r sp = tp /\
        incl sp (allModelElements sm) /\
        incl tp (allModelElements tm) /\
        matchPattern (getRules tr sm) sp = Some r ).
  Abort.

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

(* Notations *)

(* Module *)
Notation "'transformation' tname 'from' sinstance 'to' tinstance 'with' m 'as' smodel ':=' transformationbody" := (fun (tname: Phase sinstance tinstance)  (m:smodel) => transformationbody ) (right associativity, at level 60).

(* Rules *)
Notation "'[' r1 ; .. ; r2 ']'" := (cons r1 .. (cons r2 nil) ..) (right associativity, at level 9).

(* Rule *)
Notation "'rule' rulename 'from' rbody" := (rbody) (right associativity, at level 60).

(* InputPatternElement *)
Notation "'element' sid 'class' stype 'from' sinstance ',' sbody" := (BuildMultiElementRule sinstance stype (fun sid => sbody)) (right associativity, at level 60).

(* InputPatternElement *)
Notation "'element' sid 'class' stype 'from' sinstance 'when' guard 'to' outputels" := (BuildSingleElementRule sinstance stype (fun sid => (guard, outputels))) (right associativity, at level 60).

(* OutputPatternElement *)
Notation "'output' elid 'element' elname 'class' eltype 'from' tinstance := eldef 'links' refdef" := (BuildOutputPatternElement eltype elid%string eldef (fun elname => refdef))  (right associativity, at level 60).

(* OutputPatternElementReferenceDefinition *)
Notation "'reference' reftype 'from' tinstance ':=' refends" := (BuildOutputPatternElementReference tinstance reftype refends) (right associativity, at level 60).

(*  Lemma allTuples_in_allModelElements :
    forall (sm:SourceModel) (x: list SourceModelElement),
      In x (allTuples sm) -> incl x (allModelElements sm).
  Proof.
    
    
  Abort. *)
  
(*  Theorem tr_distri:
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
  Qed. *)
  
  