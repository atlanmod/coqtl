Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.
Require Import transformations.Families2Persons.Families.
Require Import transformations.Families2Persons.Persons.
Require Import transformations.Families2Persons.Families2Persons.
Require Import transformations.Families2Persons.tests.sampleFamilies.

Compute (execute Families2Persons InputModel).