Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.Certification.
Require Import core.Syntax.
Require Import core.utils.Utils.
Require Import transformations.Families2Persons.Families.
Require Import transformations.Families2Persons.Persons.
Require Import transformations.Families2Persons.Families2Persons.
Require Import transformations.Families2Persons.tests.sampleFamilies.


Theorem tr_FamiliesToPersons :
    forall (sm : FamiliesModel) (te : PersonsMetamodel_Object), 
      In te (allModelElements (execute Families2Persons sm)) ->
      (exists (se : FamiliesMetamodel_Object),
          In se (allModelElements sm) /\
          In te
            (instantiatePattern Families2Persons sm [se])).
Proof.
    intros.
    apply tr_execute_in_elements in H.
    destruct H.
    destruct H.
    destruct x.
    - contradiction H0.
    - destruct x.
      + exists f. 
        apply allTuples_incl in H.
        unfold incl in H.
        specialize (H f).
        crush.
      + exfalso. 
        specialize (allTuples_not_incl_length (f :: f0 :: x) Families2Persons sm).
        crush.
Qed.
