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
  (TransformationDef: Type) (RuleDef: Type) 
  (OutputPatternElementDef: Type) (OutputPatternElementReferenceDef: Type) 
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

      (** *** getRulesFun

              Return rules within given transformation. *)
      getRulesFun: TransformationDef -> list RuleDef;

      (** *** getOutputPatternElementsFun

              Return output pattern elements within given rule. *)
      getOutputPatternElementsFun: RuleDef -> list OutputPatternElementDef;

      (** *** getOutputPatternElementReferencesFun

              Return output pattern references within given rule *)
      getOutputPatternElementReferencesFun: OutputPatternElementDef -> list OutputPatternElementReferenceDef;

    (** ** Transformation Engine Functions *)

      (** *** executeFun

              Given a _souce model_ and a _transformation_, _execute_ should return a _target model_. *)
      executeFun: TransformationDef -> SourceModel -> TargetModel;

      (** *** matchPatternFun 

              TODO *)
      matchPatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option RuleDef;

      (** *** matchRuleOnPatternFun 

              TODO *)
      matchRuleOnPatternFun:  RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> option bool;

      (** *** instantiatePatternFun 

              TODO *)
      instantiatePatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelElement);

      (** *** instantiateRuleOnPatternFun 

              TODO *)
      instantiateRuleOnPatternFun: RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelElement); 
      
      (** *** applyPatternFun 

              TODO *)      
      applyPatternFun: TransformationDef -> SourceModel -> list SourceModelElement -> option (list TargetModelLink);
      
      (** *** applyRuleOnPatternFun 

              TODO *)      
      applyRuleOnPatternFun: RuleDef -> TransformationDef -> SourceModel -> list SourceModelElement -> list TargetModelElement -> option (list TargetModelLink);

    (** ** Theorems of Transformation Engine *)

      (** *** Soundness Theorems *)

        (** **** tr_surj_elements 

                Definition: every model element in the target model is produced by a rule application *)
        tr_surj_elements : 
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelElement),
          tm = executeFun tr sm -> In t1 (allTargetModelElements tm) ->
          (exists (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
            In r (getRulesFun tr) /\
            In t1 tp /\
            instantiateRuleOnPatternFun r tr sm sp = Some tp /\
            incl sp (allSourceModelElements sm) /\
            incl tp (allTargetModelElements tm) /\
            matchPatternFun tr sm sp = Some r );

        (** **** tr_surj_links 

                Definition: every model links in the target model is produced by a rule application *)
        tr_surj_links : 
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (t1 : TargetModelLink),
          tm = executeFun tr sm -> In t1 (allTargetModelLinks tm) ->
          (exists (sp : list SourceModelElement) (tel : list TargetModelElement) (tpl : list TargetModelLink) (r : RuleDef),
            In r (getRulesFun tr) /\
            In t1 tpl /\
            applyRuleOnPatternFun r tr sm sp tel = Some tpl /\
            incl sp (allSourceModelElements sm) /\
            incl tpl (allTargetModelLinks tm) /\
            matchPatternFun tr sm sp = Some r );

      (** *** Completeness Theorems *)

        (** **** outp_incl_elements 

                Definition: if a rule matches, then its output model elements is included in the target model *)
        outp_incl_elements :
            forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef) (tes: list TargetModelElement) ,
              tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
              matchPatternFun tr sm sp = Some r ->
              instantiateRuleOnPatternFun r tr sm sp = Some tes ->
              incl tes (allTargetModelElements tm);

        (** **** outp_incl_links 

                Definition: if a rule matches, then its output model references is included in the target model *)
        outp_incl_links :
            forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) (sp : list SourceModelElement) (r: RuleDef) (tes: list TargetModelElement) (tls: list TargetModelLink),
              tm = executeFun tr sm -> In r (getRulesFun tr) -> incl sp (allSourceModelElements sm) ->
              matchPatternFun tr sm sp = Some r ->
              instantiateRuleOnPatternFun r tr sm sp = Some tes ->
              applyRuleOnPatternFun r tr sm sp tes = Some tls ->
              incl tls (allTargetModelLinks tm);

    
      (** *** Well-formatness Theorems *)

        (** **** match_in 

                 Definition: if a source pattern matches a rule, then this rule should include in the transformation *)
        match_in :
            forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r: RuleDef),
              matchPatternFun tr sm sp = Some r -> In r (getRulesFun tr);    

        (** **** match_functional 

                 Definition: execute matchPattern on same arguments produce same result. *)
        match_functional :
            forall (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
              matchPatternFun tr sm sp = Some r1 -> matchPatternFun tr sm sp = Some r2 -> r1 = r2;

        (** **** instantiate_pattern_derivable 

                 Definition: the result of _instantiatePattern_ can be derived from _instantiateRuleOnPattern_ and _matchPattern_ *)
        instantiate_pattern_derivable : 
        forall (tr: TransformationDef) (sm : SourceModel) (tm: TargetModel) 
               (sp : list SourceModelElement) (tp : list TargetModelElement) (r : RuleDef),
          tm = executeFun tr sm -> incl tp (allTargetModelElements tm) ->
          instantiateRuleOnPatternFun r tr sm sp = Some tp ->
          matchPatternFun tr sm sp = Some r ->
          instantiatePatternFun tr sm sp = Some tp;


      (** *** Termination theorems (implicit) *)


      (** *** Correctness theorems *)

        (** **** TODO dangle_links_absent

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
  forall (TransformationDef RuleDef OutputPatternElementDef OutputPatternElementReferenceDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel: Type) (eng: TransformationEngineTypeClass TransformationDef RuleDef OutputPatternElementDef OutputPatternElementReferenceDef SourceModelElement SourceModelLink SourceModel TargetModelElement TargetModelLink TargetModel)
    (tr: TransformationDef) (sm : SourceModel) (sp : list SourceModelElement) (r1: RuleDef) (r2: RuleDef),
          matchPatternFun tr sm sp  = Some r1 -> matchPatternFun tr sm sp = Some r2 -> r1 = r2.
Proof.
    intros.
    rewrite H in H0.
    inversion H0.
    reflexivity.
Qed.