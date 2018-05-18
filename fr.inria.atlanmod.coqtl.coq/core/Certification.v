Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.CoqTL.
Require Import core.Engine.

Set Implicit Arguments.

Section Cert.

  Variables (SourceModelElement SourceModelLink SourceModelClass SourceModelReference: Type)
            (smm: Metamodel SourceModelElement SourceModelLink SourceModelClass SourceModelReference)
            (TargetModelElement TargetModelLink TargetModelClass TargetModelReference: Type)
            (tmm: Metamodel TargetModelElement TargetModelLink TargetModelClass TargetModelReference).

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
  
Definition numberOfRules (tr: Transformation) : nat
    := length ((getRules tr) (BuildModel nil nil)).

Definition RuleDef : Type := nat * Transformation.

Fixpoint matchPattern'' (tr: list Rule) (inelems: list SourceModelElement) : option nat :=
    match tr with
    | r :: rs => match matchRuleOnPattern r inelems with
                | Some op => Some (length rs)
                | None => matchPattern'' rs inelems
                end
    | nil => None
    end.

(*
Definition matchPattern' (tr: Transformation) (sp: list SourceModelElement) (sm: SourceModel) : option Rule :=
   matchPattern (getRules tr sm) sp.
*)

Fixpoint getRulesFun' {T : Type} (n : nat) (tr: T) :=
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

(*Definition getRuleDef (r : Rule) (tr : Transformation) (sm: SourceModel) : option RuleDef := None.*)

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