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
  Admitted.


End Exp.

Arguments denoteFunction: default implicits.
Arguments evalFunction: default implicits.

