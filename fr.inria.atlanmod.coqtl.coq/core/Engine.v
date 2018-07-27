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

Require Import core.utils.tTop.
Require Import core.Model.

Set Implicit Arguments.

Class TransformationEngineTypeClass 
  (Transformation: Type) (Rule: Type) 
  (OutputPatternElement: Type) (OutputPatternElementReference: Type) 
  (SourceModelElement: Type) (SourceModelLink: Type) (SourceModel: Type) 
  (TargetModelElement: Type) (TargetModelLink: Type) (TargetModel: Type) :=
  {
    (** ** Functions of Models *)

      (** *** allSourceModelElements

              Return model elements of the source model. *)
      allSourceModelElements: SourceModel -> list SourceModelElement;
      
      (** *** allSourceModelLinks

              Return model links of the source model. *)
      allSourceModelLinks: SourceModel -> list SourceModelLink;
      
      (** *** allTargetModelElements

              Return model element of the target model. *)
      allTargetModelElements: TargetModel -> list TargetModelElement;
      
      (** *** allTargetModelLinks

              Return model element of the target model. *)
      allTargetModelLinks: TargetModel -> list TargetModelLink;

    (** ** Transformation Engine Accessors *)

      (** *** getRules

              Return rules within given transformation. *)
      getRules: Transformation -> list Rule;

      (** *** getOutputPatternElements

              Return output pattern elements within given rule. *)
      getOutputPatternElements: Rule -> list OutputPatternElement;

      (** *** getOutputPatternElementReferences

              Return output pattern references within given rule *)
      getOutputPatternElementReferences: OutputPatternElement -> list OutputPatternElementReference;

    (** ** Transformation Engine Functions *)

      (** *** execute

              Given a _souce model_ and a _transformation_, _execute_ should return a _target model_. *)
      execute: Transformation -> SourceModel -> TargetModel;

      (** *** matchPattern 

              TODO *)
      matchPattern: Transformation -> SourceModel -> list SourceModelElement -> option Rule;

      (** *** matchRuleOnPattern 

              TODO *)
      matchRuleOnPattern:  Rule -> Transformation -> SourceModel -> list SourceModelElement -> option bool;

      (** *** instantiatePattern 

              TODO *)
      instantiatePattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);

      (** *** instantiateRuleOnPattern 

              TODO *)
      instantiateRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
      
      (** *** applyPattern 

              TODO *)      
      applyPattern: Transformation -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
      
      (** *** applyRuleOnPattern 

              TODO *)      
      applyRuleOnPattern: Rule -> Transformation -> SourceModel -> list SourceModelElement -> list TargetModelElement -> option (list TargetModelLink);

    (** ** Theorems of Transformation Engine *)

      (** *** Soundness Theorems *)

        (** **** tr_surj_elements 

                Definition: every model element in the target model is produced by a rule application *)
        tr_surj_elements : 
        forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
          tm = execute tr sm -> In t1 (allTargetModelElements tm) ->
          (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : Rule),
            In r (getRules tr) /\
            In t1 tp /\
            instantiateRuleOnPattern r tr sm sp = Some tp /\
            incl sp (allSourceModelElements sm) /\
            incl tp (allTargetModelElements tm) /\
            matchPattern tr sm sp = Some r );

        (** **** tr_surj_links 

                Definition: every model links in the target model is produced by a rule application *)
        tr_surj_links : 
        forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
          tm = execute tr sm -> In t1 (allTargetModelLinks tm) ->
          (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : Rule),
            In r (getRules tr) /\
            In t1 tpl /\
            applyRuleOnPattern r tr sm sp tel = Some tpl /\
            incl sp (allSourceModelElements sm) /\
            incl tpl (allTargetModelLinks tm) /\
            matchPattern tr sm sp = Some r );

      (** *** Completeness Theorems *)

        (** **** outp_incl_elements 

                Definition: if a rule matches, then its output model elements is included in the target model *)
        outp_incl_elements :
            forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: Rule) (tes: list TargetModelElement) ,
              tm = execute tr sm -> In r (getRules tr) -> incl sp (allSourceModelElements sm) ->
              matchPattern tr sm sp = Some r ->
              instantiateRuleOnPattern r tr sm sp = Some tes ->
              incl tes (allTargetModelElements tm);

        (** **** outp_incl_links 

                Definition: if a rule matches, then its output model references is included in the target model *)
        outp_incl_links :
            forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: Rule) (tes: list TargetModelElement) (tls: list TargetModelLink),
              tm = execute tr sm -> In r (getRules tr) -> incl sp (allSourceModelElements sm) ->
              matchPattern tr sm sp = Some r ->
              instantiateRuleOnPattern r tr sm sp = Some tes ->
              applyRuleOnPattern r tr sm sp tes = Some tls ->
              incl tls (allTargetModelLinks tm);

    
      (** *** Well-formedness Theorems *)

        (** **** match_in 

                 Definition: if a source pattern matches a rule, then this rule should include in the transformation *)
        match_in :
            forall (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r: Rule),
              matchPattern tr sm sp = Some r -> In r (getRules tr);    

        (** **** match_functional 

                 Definition: execute matchPattern on same arguments produce same result. *)
        match_functional :
            forall (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r1: Rule) (r2: Rule),
              matchPattern tr sm sp = Some r1 -> matchPattern tr sm sp = Some r2 -> r1 = r2;

        (** **** instantiate_pattern_derivable 

                 Definition: the result of _instantiatePattern_ can be derived from _instantiateRuleOnPattern_ and _matchPattern_ *)
        instantiate_pattern_derivable : 
        forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) 
               (sp : list SourceModelElement) (tp : list TargetModelElement) (r : Rule),
          tm = execute tr sm ->
          instantiateRuleOnPattern r tr sm sp = Some tp ->
          matchPattern tr sm sp = Some r ->
          instantiatePattern tr sm sp = Some tp;

       (** **** apply_pattern_derivable **)
        
        apply_pattern_derivable : 
        forall (tr: Transformation) (sm : SourceModel) (tm: TargetModel) 
               (sp : list SourceModelElement) (tp : list TargetModelElement) (tls : list TargetModelLink) (r : Rule),
          tm = execute tr sm ->
          applyRuleOnPattern r tr sm sp tp = Some tls ->
          instantiateRuleOnPattern r tr sm sp = Some tp ->
          matchPattern tr sm sp = Some r ->
          applyPattern tr sm sp = Some tls;
        
      (** *** Termination theorems (implicit) *)


      (** *** Correctness theorems *)

        (** **** TODO no_dangling_links

                 Definition: all elements refered by links of target model, should be present in models of target model.
                 Note: CoqTL does not hold on this property yet *)


      (** *** Convergence theorems *)

        (** **** TODO tr_converge

                 Definition: apply rules in different order get same output. 
                 Note: CoqTL does not hold on this property yet *)


      (** *** Additivity theorems *)

        (** **** TODO tr_additivity

                 Definition: remove binding, the links is a subset of tm created before. 
                 See: Soichiro Hidaka, Frédéric Jouault, Massimo Tisi. On Additivity in Transformation Languages. MODELS 2017. *)

  }.

Theorem match_functionality :  
  forall (Transformation Rule OutputPatternElement OutputPatternElementReference SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel: Type) (eng: TransformationEngineTypeClass Transformation Rule OutputPatternElement OutputPatternElementReference SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel)
    (tr: Transformation) (sm : SourceModel) (sp : list SourceModelElement) (r1: Rule) (r2: Rule),
          matchPattern tr sm sp  = Some r1 -> matchPattern tr sm sp = Some r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.