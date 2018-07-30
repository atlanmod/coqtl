Require Import String.
Require Import List.
Require Import Multiset.
Require Import ListSet.
Require Import Omega.

Require Import core.utils.tTop.
Require Import core.Notations.
Require Import core.CoqTL.
Require Import core.Model.
Require Import core.utils.CpdtTactics.

Require Import examples.Class2RelationalMV.Class2Relational.
Require Import examples.Class2RelationalMV.ClassMetamodel.
Require Import examples.Class2RelationalMV.RelationalMetamodel.


Theorem information_preservation :
  forall (rm : Model RelationalMetamodel_EObject RelationalMetamodel_ELink)
    (cm: Model ClassMetamodel_EObject ClassMetamodel_ELink),
    rm = execute Class2Relational cm ->
    forall (a: Attribute),
      In (ClassMetamodel_toEObject a) (allModelElements cm) ->
      exists (c: Column),
        In (RelationalMetamodel_toEObject c) (allModelElements rm) /\
        getColumnName c = getAttributeName a.
  intros.
  destruct a eqn:a_dest.
  destruct b eqn:b_dest.
  * assert (incl [RelationalMetamodel_toEObjectOfEClass ColumnEClass
            (BuildColumn (s ++ "_MA2C_col") s0);
         RelationalMetamodel_toEObjectOfEClass TableEClass
           (BuildTable (s ++ "_MA2C_pivot")
              (String "P"
                 (String "i"
                    (String "v" (String "o" (String "t" s0))))));
         RelationalMetamodel_toEObjectOfEClass ColumnEClass
           (BuildColumn (s ++ "_MA2C_psrc") "key");
         RelationalMetamodel_toEObjectOfEClass ColumnEClass
           (BuildColumn (s ++ "_MA2C_ptrg") s0)] (allModelElements rm)). {
      apply outp_incl_elements2 with (tr:=Class2Relational) (sm:=cm) (sp:= [ClassMetamodel_toEObject a]).
      * crush.
      * apply incl_cons.
        ** crush.
        ** unfold incl. crush.
      * crush.    
    }
    exists (BuildColumn (s ++ "_MA2C_col") s0).
    split.
    ** crush.
    ** crush.
  * assert (incl [RelationalMetamodel_toEObjectOfEClass ColumnEClass
                                                        (BuildColumn (s ++ "_SA2C_col") s0)] (allModelElements rm)). {
      apply outp_incl_elements2 with (tr:=Class2Relational) (sm:=cm) (sp:= [ClassMetamodel_toEObject a]).
      * crush.
      * apply incl_cons.
        ** crush.
        ** unfold incl. crush.
      * crush.
    }
    exists (BuildColumn (s ++ "_SA2C_col") s0).
    split.
    ** crush.
    ** crush.
Qed.