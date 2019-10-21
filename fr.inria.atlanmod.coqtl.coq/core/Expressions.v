Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Section Exp.

  Variables (ModelElement ModelLink ModelClass ModelReference: Type)
            (mm: Metamodel ModelElement ModelLink ModelClass ModelReference).
    
  Fixpoint denoteFunction (sclasses : list ModelClass) (otype: Type) :=
    match sclasses with
    | nil => otype
    | cons class classes' => (denoteModelClass class) -> denoteFunction classes' otype
    end.

  Fixpoint evalFunctionFix (intypes: list ModelClass) (otype: Type) (f: denoteFunction intypes otype) (el: list ModelElement) : option otype.
  Proof.
    destruct intypes eqn:intypes1, el eqn:el1.
    - exact (Some f).
    - exact None.
    - exact None.
    - destruct (toModelClass m m0) eqn:tmc.
      + destruct l eqn:intypes2, l0 eqn:el2.
        * exact (Some (f d)).
        * exact None.
        * exact None.
        * rewrite <- intypes2 in f.
          exact (evalFunctionFix l otype (f d) l0).
      + exact None.
  Defined.

  Definition evalFunction (m: Model ModelElement ModelLink) (intypes: list ModelClass) (otype: Type) (f: (Model ModelElement ModelLink) -> (denoteFunction intypes otype)) (el: list ModelElement) : option otype :=
    evalFunctionFix intypes otype (f m) el.

  Lemma evalFunctionFix_intypes_el_neq:
    forall intypes otype f el,
      length intypes <> length el ->
        evalFunctionFix intypes otype f el = None.
  Proof.
    intros.
    generalize dependent el.
    induction intypes.        
    - intros. destruct el.
      + crush.
      + crush.  
    - intros.
      induction el.
      + crush.
      + destruct (toModelClass a a0) eqn:tmc.
        * simpl. rewrite tmc.
          destruct intypes eqn:intypes2, el eqn:el2.
          ** crush.
          ** crush.
          ** crush.
          ** apply  IHintypes. simpl. simpl in H. Search (S _ <> S _).
             apply -> Nat.succ_inj_wd_neg in H.
             exact H.            
        * simpl. rewrite tmc. auto.
  Qed.
  
  Lemma evalFunctionFix_intypes_el_neq_contraposition:
    forall intypes otype f el,
        evalFunctionFix intypes otype f el <> None ->
          length intypes = length el.
  Proof.
    intros intypes otype f el.
    specialize (evalFunctionFix_intypes_el_neq intypes otype f el).
    intro.
    specialize  (contraposition) with (q:=(evalFunctionFix intypes otype f el) = None) (p:=Datatypes.length intypes <> Datatypes.length el).
    intros.
    crush.
  Qed.

End Exp.

Arguments denoteFunction: default implicits.
Arguments evalFunction: default implicits.

