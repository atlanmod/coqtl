Require Import String.
Require Import List.
Require Import CoqTL.
Require Import ClassMetamodel.
Require Import RelationalMetamodel.
Require Import Class2Relational.
Require Import PersonModel.
Require Import Utils_Print.

(* Require Import Class2RelationalVerif. *)

Compute (execute Class2Relational PersonModel).

Definition model := (execute Class2Relational PersonModel).


Fixpoint findRoot (l : list RelationalMetamodel_EObject) : option RelationalMetamodel_EObject := 
 match l with
 | e :: l' => match RelationalMetamodel_getEClass e with
               | TableClass => Some e
               | ColumnClass => findRoot l'
              end
 | nil => None
 end.

Definition TabletoString (t: Table) : string :=
  match t with
  | BuildTable id name => 
      " id=" ++ (natToString id) ++ " name='"++name++"'"
  end.

Fixpoint PrintEObject (rm: RelationalModel) (e: RelationalMetamodel_EObject) (lv: nat) (isRef: bool) : string := 
  match RelationalMetamodel_getEClass e with
   | TableClass => match toRelationalMetamodel_EClass TableClass e with
                    | Some t => "<Table" ++ TabletoString t ++ ">"++ "</Table>"
                    | None => "ERROR"
                   end
   | ColumnClass => "ERROR"
  end.




Definition PrintXMI (rm : RelationalModel) : string :=
  match (findRoot (allModelElements rm)) with
  | None => "No Root Element Found."
  | Some e => PrintEObject rm e 0 false
  end.
  


  
  
Compute (PrintXMI model).

