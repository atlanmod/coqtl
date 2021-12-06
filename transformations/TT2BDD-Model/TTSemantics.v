Require Import TT2BDD.TT.
Require Import BoolEq.
Require Import core.Model.
Require Import String.
Require Import List.
Require Import Utils.

Definition matchInputCell 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (cell : Cell)
    (ins: list (string*bool)):
        bool :=
    match Cell_getPort cell ttm with 
    | Some (Build_Abstract_Port InputPortEClass p) => 
        existsb (fun input => 
            andb (String.eqb (fst input) (InputPort_getName p)) 
                (Bool.eqb (snd input) (Cell_getValue cell))) 
            ins
    | _ => true
    end.

Definition matchRow 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (row : Row)
    (ins: list (string*bool)): 
        bool :=
    match Row_getCells row ttm with
    | Some cells => forallb (fun cell => matchInputCell ttm cell ins) cells
    | _ => true
    end.

Definition outputCells 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (row : Row):
        list Cell :=
    match Row_getCells row ttm with
    | Some cells => 
        filter (fun cell => 
            match Cell_getPort cell ttm with 
            | Some (Build_Abstract_Port OutputPortEClass _) => true
            | _ => false
            end
            ) cells
    | _ => nil
    end.

Definition cellToPair 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (cell : Cell): 
        string*bool :=
    match Cell_getPort cell ttm with 
        | Some (Build_Abstract_Port OutputPortEClass p) => (OutputPort_getName p,Cell_getValue cell)
        | Some (Build_Abstract_Port InputPortEClass p) => (InputPort_getName p,Cell_getValue cell)
        | _ => (""%string, Cell_getValue cell)
    end.

Definition outputOfRow 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (row : Row):
        list (string*bool) :=
    match Row_getCells row ttm with
    | Some cells => 
        map (cellToPair ttm) (outputCells ttm row)
    | _ => nil
    end.

Definition eval 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (tt : TruthTable)
    (ins: list (string*bool)): 
        list (string*bool) :=
    match TruthTable_getRows tt ttm with 
    | Some rows => 
        flat_map (outputOfRow ttm)  (filter (fun row => matchRow ttm row ins) rows)
    | _ => nil
    end.

Definition valueOf 
    (portValues: list (string*bool))
    (portName: string)
    :=
    let values := (nodup bool_dec (map snd (filter (fun p => String.eqb (fst p) portName) portValues))) in
    match values with
    | false :: nil => Some false
    | true :: nil => Some true
    | _ => None
    end.

Definition allInputPorts 
    (ttm: Model TTMetamodel_EObject TTMetamodel_ELink)
    (tt : TruthTable) :=
    filter 
        (fun port => match port with
        | (Build_Abstract_Port InputPortEClass p) => true 
        | _ => false
        end)
        (optionListToList (TruthTable_getPorts tt ttm)).