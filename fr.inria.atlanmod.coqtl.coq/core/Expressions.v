Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.Metamodel.
Require Import core.Model.
Require Import core.Engine.
Require Import core.utils.TopUtils.
Require Import core.utils.CpdtTactics.

Section Exp.

  Variables (ModelElement ModelLink ModelClass ModelReference: Type)
            (mm: Metamodel ModelElement ModelLink ModelClass ModelReference).
    
  Fixpoint denoteFuncOfClasses (sclasses : list ModelClass) (otype: Type) :=
    match sclasses with
    | nil => otype
    | cons class classes' => (denoteModelClass class) -> denoteFuncOfClasses classes' otype
    end.

  Fixpoint evalFuncOfClassesFix (intypes: list ModelClass) (otype: Type) (f: denoteFuncOfClasses intypes otype) (el: list ModelElement) : option otype.
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
          exact (evalFuncOfClassesFix l otype (f d) l0).
      + exact None.
  Defined.

  Definition evalFuncOfClasses (m: Model ModelElement ModelLink) (intypes: list ModelClass) (otype: Type) (f: (Model ModelElement ModelLink) -> (denoteFuncOfClasses intypes otype)) (el: list ModelElement) : option otype :=
    evalFuncOfClassesFix intypes otype (f m) el.

End Exp.

Arguments denoteFuncOfClasses: default implicits.
Arguments evalFuncOfClasses: default implicits.


