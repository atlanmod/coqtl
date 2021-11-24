Require Import String.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import Bool.

Require Import core.utils.Utils.
Require Import core.Model.
Require Import core.Semantics.
Require Import core.modeling.Parser.

Require Import transformations.RSS2ATOM.RSS.
Require Import transformations.RSS2ATOM.ATOM.
Require Import transformations.RSS2ATOM.RSS2ATOM.
Require Import transformations.RSS2ATOM.tests.Exemple1RSS.
Require Import transformations.RSS2ATOM.tests.Exemple1ATOM.

Compute 
  (Model_beq beq_ATOMMetamodel_Object beq_ATOMMetamodel_Link 
    (execute (parse RSS2ATOM) Exemple1RSS)
    Exemple1ATOM).
