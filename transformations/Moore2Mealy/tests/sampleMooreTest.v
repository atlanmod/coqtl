Require Import String.
Require Import List.

Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.ModelingSemantics.
Require Import core.modeling.ConcreteSyntax.
Require Import core.utils.Utils.

Require Import transformations.Moore2Mealy.Moore.
Require Import transformations.Moore2Mealy.Mealy.
Require Import transformations.Moore2Mealy.Moore2Mealy.
Require Import transformations.Moore2Mealy.tests.sampleMoore.

Compute (execute Moore2Mealy InputModel).