(************************************************************************)
(*         *   The NaoMod Development Team                              *)
(*  v      *   INRIA, CNRS and contributors - Copyright 2017-2019       *)
(* <O___,, *       (see CREDITS file for the list of authors)           *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

(**
 This file is the type class for relational transformation engine.
 
 We give functions signatures that instaniated transformation engines should
    generally have. We also introduce several useful theorems enforced on these 
    functions in order to certify instaniated transformation engines.

 An example instaniated transformation engine is in [core.Certification].        **)


(*********************************************************)
(** * Type Class for relational Transformation Engines   *)
(*********************************************************)

Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Expressions.

Scheme Equality for list.

Set Implicit Arguments.



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

    smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference;
    tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference;

    SourceModel := Model SourceModelElement SourceModelLink;
    TargetModel := Model TargetModelElement TargetModelLink;

    Transformation: Type;
    Rule: Type;
    OutputPatternElement: Type;
    OutputPatternElementReference: Type;
    TraceLink: Type;

    (** ** Accessors *)

    Transformation_getRules: Transformation -> list Rule;

    Rule_getInTypes: Rule -> list SourceModelClass;    
    Rule_getOutputPatternElements: Rule -> list OutputPatternElement;

    OutputPatternElement_getOutputElementReferences: OutputPatternElement -> list OutputPatternElementReference;

    TraceLink_getSourcePattern: TraceLink -> list SourceModelElement;
    TraceLink_getIterator: TraceLink -> nat;
    TraceLink_getName: TraceLink -> string;
    TraceLink_getTargetElement: TraceLink -> TargetModelElement;


    (** ** maxArity *)

    maxArity (tr: Transformation) : nat :=
      max (map (length (A:=SourceModelClass)) (map Rule_getInTypes (Transformation_getRules tr)));

    allTuples (tr: Transformation) (sm : SourceModel) :list (list SourceModelElement) :=
      tuples_up_to_n (allModelElements sm) (maxArity tr);

    (** ** Functions *)
    
    execute: Transformation -> SourceModel -> TargetModel;
    
    matchPattern: Transformation -> SourceModel -> list SourceModelElement -> list Rule;
    matchRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> bool;

    instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> list TargetModelElement;
    instantiateRuleOnPattern: Rule -> SourceModel -> list SourceModelElement -> list TargetModelElement; 
    instantiateIterationOnPattern: Rule -> SourceModel -> list SourceModelElement -> nat -> list TargetModelElement;
    instantiateElementOnPattern: OutputPatternElement -> SourceModel -> list SourceModelElement -> nat -> option TargetModelElement;
    
    applyPattern: Transformation -> SourceModel -> list SourceModelElement -> list TargetModelLink;
    applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> list TargetModelLink;
    applyIterationOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TargetModelLink;
    applyElementOnPattern: OutputPatternElement -> Transformation -> SourceModel -> list SourceModelElement -> nat -> list TargetModelLink;
    applyReferenceOnPattern: OutputPatternElementReference -> Transformation -> SourceModel -> list SourceModelElement -> nat -> TargetModelElement -> option TargetModelLink;
    
    evalOutputPatternElementExpr: SourceModel -> list SourceModelElement -> nat -> OutputPatternElement -> option TargetModelElement;
    evalIteratorExpr: Rule -> SourceModel -> list SourceModelElement -> nat;
    evalOutputPatternLinkExpr: SourceModel -> list SourceModelElement -> TargetModelElement -> nat -> list TraceLink -> OutputPatternElementReference -> option TargetModelLink;
    evalGuardExpr: Rule->SourceModel->list SourceModelElement->option bool;

    trace: Transformation -> SourceModel -> list TraceLink; 

    resolveAll: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat),
        option (list (denoteModelClass type));
    resolve: forall (tr: list TraceLink) (sm: SourceModel) (name: string)
             (type: TargetModelClass) (sp: list SourceModelElement) (iter : nat), option (denoteModelClass type);

    (** ** Theorems *)

    (** ** execute *)

    tr_execute_in_elements :
      forall (tr: Transformation) (sm : SourceModel) (te : TargetModelElement),
      In te (allModelElements (execute tr sm)) <->
      (exists (sp : list SourceModelElement),
          In sp (allTuples tr sm) /\
          In te (instantiatePattern tr sm sp));

    tr_execute_in_links :
      forall (tr: Transformation) (sm : SourceModel) (tl : TargetModelLink),
        In tl (allModelLinks (execute tr sm)) <->
        (exists (sp : list SourceModelElement),
            In sp (allTuples tr sm) /\
            In tl (applyPattern tr sm sp));

    (** ** matchPattern *)

    tr_matchPattern_in :
       forall (tr: Transformation) (sm : SourceModel),
         forall (sp : list SourceModelElement)(r : Rule),
           In r (matchPattern tr sm sp) <->
             In r (Transformation_getRules tr) /\
             matchRuleOnPattern r sm sp = true;

    (*tr_matchPattern_None : 
        forall (tr: Transformation) (sm : SourceModel) 
          (sp: list SourceModelElement),
            length sp > maxArity tr ->
              matchPattern tr sm sp = nil;*)

    (** ** matchRuleOnPattern *)

    tr_matchRuleOnPattern_Leaf :
    forall (tr: Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement),
      matchRuleOnPattern r sm sp =
       match evalGuardExpr r sm sp with Some true => true | _ => false end;

    (*tr_matchRuleOnPattern_None :
        forall (tr: Transformation) (sm : SourceModel) 
          (r: Rule) (sp: list SourceModelElement),
           length sp <> length (Rule_getInTypes r) ->
            matchRuleOnPattern r tr sm sp = None;*)

    (** ** instantiatePattern *)

    tr_instantiatePattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
        In te (instantiatePattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In te (instantiateRuleOnPattern r sm sp));

    (*tr_instantiatePattern_non_None : 
     forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
      instantiatePattern tr sm sp <> None <->
      (exists (r: Rule),
          In r (matchPattern tr sm sp) /\
          instantiateRuleOnPattern r tr sm sp <> None);
       
    tr_instantiatePattern_None : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        instantiatePattern tr sm sp = None;*)

    (** ** instantiateRuleOnPattern *)

    tr_instantiateRuleOnPattern_in :
    forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement),
      In te (instantiateRuleOnPattern r sm sp) <->
      (exists (i: nat),
          In i (indexes (evalIteratorExpr r sm sp)) /\
          In te (instantiateIterationOnPattern r sm sp i));

    (*tr_instantiateRuleOnPattern_non_None : 
     forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement),
      instantiateRuleOnPattern r tr sm sp <> None <->
      (exists (i: nat),
          i < length (evalIterator r sm sp) /\
          instantiateIterationOnPattern r sm sp i <> None);*)    

   (** ** instantiateIterationOnPattern *)

    tr_instantiateIterationOnPattern_in : 
      forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (te : TargetModelElement) (i:nat),
        In te (instantiateIterationOnPattern r sm sp i)
        <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            instantiateElementOnPattern ope sm sp i = Some te);

    (*tr_instantiateIterationOnPattern_non_None : 
     forall (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
      instantiateIterationOnPattern r sm sp i <> None <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
          In ope (getOutputPattern r) /\ 
          instantiateElementOnPattern ope sm sp i <> None);
    
    tr_instantiateElementOnPattern_None : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
        length sp <> length (Rule_getInTypes r) ->
        instantiateElementOnPattern ope sm sp i = None;*)

    (** ** instantiateElementOnPattern *)

    tr_instantiateElementOnPattern_leaf:
        forall (o: OutputPatternElement) (sm: SourceModel) (sp: list SourceModelElement) (iter: nat),
          instantiateElementOnPattern o sm sp iter = evalOutputPatternElementExpr sm sp iter o;

    (*tr_instantiateElementOnPattern_Leaf :
      forall (sm : SourceModel)
        (tr: Transformation) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
        instantiateElementOnPattern ope sm sp i =
        m <- matchRuleOnPattern r tr sm sp;
        matched <- if m then Some true else None;
        it <- nth_error (evalIterator r sm sp) i;
        r0 <- evalFunction smm sm (Rule_getInTypes r)
           (denoteModelClass (getOutType ope))
           (getOutPatternElement ope it) sp;
        Some (toModelElement (getOutType ope) r0);

    tr_instantiateElementOnPattern_None_iterator : 
      forall (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
        i >= length (evalIterator r sm sp) ->
        instantiateElementOnPattern ope sm sp i = None;*) 
    
    (** ** applyPattern *)

    tr_applyPattern_in :
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyPattern tr sm sp) <->
        (exists (r : Rule),
            In r (matchPattern tr sm sp) /\
            In tl (applyRuleOnPattern r tr sm sp));

    (*
    tr_applyPattern_non_None : 
     forall  (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyPattern tr sm sp <> None <->
      (exists  (r : Rule),
         In r (matchPattern tr sm sp) /\
         applyRuleOnPattern r tr sm sp <> None);
    
    tr_applyPattern_None : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement),
        length sp > maxArity tr ->
        applyPattern tr sm sp = None;*)

    (** ** applyRuleOnPattern *)

    tr_applyRuleOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink),
        In tl (applyRuleOnPattern r tr sm sp) <->
        (exists (i: nat),
            In i (indexes (evalIteratorExpr r sm sp)) /\
            In tl (applyIterationOnPattern r tr sm sp i));

    (*
    tr_applyRuleOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) ,
       applyRuleOnPattern r tr sm sp <> None <->
      (exists (i: nat),
        i < length (evalIterator r sm sp) /\
        applyIterationOnPattern r tr sm sp i <> None );*)

    (** ** applyIterationOnPattern *)

    tr_applyIterationOnPattern_in : 
      forall (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) (i:nat),
        In tl (applyIterationOnPattern r tr sm sp i) <->
        (exists (ope: OutputPatternElement),
            In ope (Rule_getOutputPatternElements r) /\ 
            In tl (applyElementOnPattern ope tr sm sp i));

    (*
    tr_applyIterationOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat),
       applyIterationOnPattern r tr sm sp i <> None <->
      (exists (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
            In ope (getOutputPattern r) /\ 
            applyElementOnPattern ope tr sm sp i <> None);*)

    (** ** applyElementOnPattern *)

    tr_applyElementOnPattern_in : 
      forall (tr: Transformation) (sm : SourceModel) (sp: list SourceModelElement) (tl : TargetModelLink) 
             (i:nat) (ope: OutputPatternElement),
        In tl (applyElementOnPattern ope tr sm sp i ) <->
        (exists (oper: OutputPatternElementReference) (te: TargetModelElement),
            In oper (OutputPatternElement_getOutputElementReferences ope) /\ 
            (evalOutputPatternElementExpr sm sp i ope) = Some te /\
            applyReferenceOnPattern oper tr sm sp i te = Some tl);
    
    (*    
    tr_applyElementOnPattern_non_None : 
     forall  (tr: Transformation) (r : Rule) (sm : SourceModel) (sp: list SourceModelElement) (i:nat) (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r)),
       applyElementOnPattern ope tr sm sp i <> None <->
      (exists(oper: OutputPatternElementReference (Rule_getInTypes r) (getIteratorType r) (getOutType ope)),
          In oper (OutputPatternElement_getOutputElementReferences ope) /\ 
          applyReferenceOnPattern oper tr sm sp i <> None);*)

    (** ** applyReferenceOnPattern *)

    tr_applyReferenceOnPatternTraces_leaf : 
          forall (oper: OutputPatternElementReference)
                 (tr: Transformation)
                 (sm: SourceModel)
                 (sp: list SourceModelElement) (iter: nat) (te: TargetModelElement) (tls: list TraceLink),
            applyReferenceOnPattern oper tr sm sp iter te  = evalOutputPatternLinkExpr sm sp te iter (trace tr sm) oper;

    (*tr_applyReferenceOnPattern_Leaf :
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (Rule_getInTypes r) (getIteratorType r) (getOutType ope)),
        applyReferenceOnPattern oper tr sm sp i =
        m <- matchRuleOnPattern r tr sm sp;
        matched <- if m then Some true else None;
        it <- nth_error (evalIterator r sm sp) i;
        l <- evalOutputPatternElement sm sp it ope;
        r0 <- evalFunction smm sm (Rule_getInTypes r)
           (denoteModelClass (getOutType ope) -> option (denoteModelReference (getRefType oper)))
           (getOutputReference oper (matchTransformation tr) it) sp;
        t <- toModelClass (getOutType ope) l;
        s <- r0 t;
        Some (toModelLink (getRefType oper) s);

    tr_applyReferenceOnPattern_None : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (Rule_getInTypes r) (getIteratorType r) (getOutType ope)),
        length sp <> length (Rule_getInTypes r) ->
        applyReferenceOnPattern oper tr sm sp i = None;
        
    tr_applyReferenceOnPattern_None_iterator : 
      forall (tr:Transformation) (sm : SourceModel) (r: Rule) (sp: list SourceModelElement) (i : nat)
        (ope: OutputPatternElement (Rule_getInTypes r) (getIteratorType r))
        (oper: OutputPatternElementReference (Rule_getInTypes r) (getIteratorType r) (getOutType ope)),
        i >= length (evalIterator r sm sp) ->
        applyReferenceOnPattern oper tr sm sp i = None;*)

    (** ** maxArity *)

    (*tr_maxArity_in :
    forall (tr: Transformation) (r: Rule),
      In r (Transformation_getRules tr) ->
      maxArity tr >= length (Rule_getInTypes r);*)

    (** ** resolve *)

    tr_resolveAll_in:
    forall (tls: list TraceLink) (sm: SourceModel) (name: string)
      (type: TargetModelClass) (sps: list(list SourceModelElement)) (iter: nat)
      (te: denoteModelClass type),
      (exists tes: list (denoteModelClass type),
          resolveAll tls sm name type sps iter = Some tes /\ In te tes) <->
      (exists (sp: list SourceModelElement),
          In sp sps /\
          resolve tls sm name type sp iter = Some te);

    tr_resolve_Leaf:
    forall (tls:list TraceLink) (sm : SourceModel) (name: string) (type: TargetModelClass)
      (sp: list SourceModelElement) (iter: nat) (x: denoteModelClass type),
      resolve tls sm name type sp iter = return x ->
       (exists (tl : TraceLink),
         In tl tls /\
         Is_true (list_beq SourceModelElement beq_ModelElement (TraceLink_getSourcePattern tl) sp) /\
         ((TraceLink_getIterator tl) = iter) /\ 
         ((TraceLink_getName tl) = name)%string /\
         (toModelClass type (TraceLink_getTargetElement tl) = Some x));

  }.
