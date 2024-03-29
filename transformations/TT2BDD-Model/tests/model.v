(********************************************************************
	@name Coq declarations for model
	@date 2020/09/30 13:18:48
	@description Automatically generated by XMI2Coq transformation.
 ********************************************************************)
		 
Require Import List.
Require Import core.Model.
Require Import String.
Require Import transformations.TT2BDD.TT.


Definition InputModel : Model TTMetamodel_EObject TTMetamodel_ELink :=
	(Build_Model
		(
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "769530879_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "482052083_InputPort" "" "a")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1234250905_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port InputPortEClass (BuildInputPort "1720339_InputPort" "" "b")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "38262958_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1427040229_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1353530305_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "574268151_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement PortEClass (Build_Abstract_Port OutputPortEClass (BuildOutputPort "460201727_OutputPort" "" "s")))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1217875525_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement TruthTableEClass (BuildTruthTable "170144208_TruthTable" "" "Test"))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "364639279_Cell" "" false))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1813187653_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1832532108_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "16868310_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1881901842_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "1787079037_Cell" "" true))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "1604002113_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement RowEClass (BuildRow "812586739_Row" ""))) :: 
		(Build_TTMetamodel_EObject LocatedElementEClass (Build_Abstract_LocatedElement CellEClass (BuildCell "585324508_Cell" "" true))) :: 
		nil)
		(
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "769530879_Cell" "" false)  (BuildRow "16868310_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "769530879_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1234250905_Cell" "" false)  (BuildRow "812586739_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1234250905_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "460201727_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "38262958_Cell" "" false)  (BuildRow "1604002113_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "38262958_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1427040229_Cell" "" false)  (BuildRow "16868310_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1427040229_Cell" "" false)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "460201727_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1353530305_Cell" "" false)  (BuildRow "1813187653_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1353530305_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "574268151_Cell" "" true)  (BuildRow "1813187653_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "574268151_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1720339_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1217875525_Cell" "" true)  (BuildRow "1604002113_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1217875525_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1720339_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink TruthTablePortsEReference (BuildTruthTablePorts  (BuildTruthTable "170144208_TruthTable" "" "Test") ( (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "a") ) ::  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1720339_Port" "" "b") ) ::  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "460201727_Port" "" "s") ) :: nil ))) ::
		(Build_TTMetamodel_ELink TruthTableRowsEReference (BuildTruthTableRows  (BuildTruthTable "170144208_TruthTable" "" "Test") ( (BuildRow "812586739_Row" "") ::  (BuildRow "16868310_Row" "") ::  (BuildRow "1604002113_Row" "") ::  (BuildRow "1813187653_Row" "") :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "364639279_Cell" "" false)  (BuildRow "16868310_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "364639279_Cell" "" false)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1720339_Port" "" "b") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1813187653_Row" "")  (BuildTruthTable "170144208_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1813187653_Row" "") ( (BuildCell "1353530305_Cell" "" false) ::  (BuildCell "574268151_Cell" "" true) ::  (BuildCell "1832532108_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1832532108_Cell" "" true)  (BuildRow "1813187653_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1832532108_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "460201727_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "16868310_Row" "")  (BuildTruthTable "170144208_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "16868310_Row" "") ( (BuildCell "769530879_Cell" "" false) ::  (BuildCell "364639279_Cell" "" false) ::  (BuildCell "1427040229_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1881901842_Cell" "" true)  (BuildRow "812586739_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1881901842_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "482052083_Port" "" "a") ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "1787079037_Cell" "" true)  (BuildRow "1604002113_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "1787079037_Cell" "" true)  (Build_Abstract_Port OutputPortEClass  (BuildOutputPort "460201727_Port" "" "s") ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "1604002113_Row" "")  (BuildTruthTable "170144208_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "1604002113_Row" "") ( (BuildCell "38262958_Cell" "" false) ::  (BuildCell "1217875525_Cell" "" true) ::  (BuildCell "1787079037_Cell" "" true) :: nil ))) ::
		(Build_TTMetamodel_ELink RowOwnerEReference (BuildRowOwner  (BuildRow "812586739_Row" "")  (BuildTruthTable "170144208_TruthTable" "" "Test"))) ::
		(Build_TTMetamodel_ELink RowCellsEReference (BuildRowCells  (BuildRow "812586739_Row" "") ( (BuildCell "1881901842_Cell" "" true) ::  (BuildCell "585324508_Cell" "" true) ::  (BuildCell "1234250905_Cell" "" false) :: nil ))) ::
		(Build_TTMetamodel_ELink CellOwnerEReference (BuildCellOwner  (BuildCell "585324508_Cell" "" true)  (BuildRow "812586739_Row" ""))) ::
		(Build_TTMetamodel_ELink CellPortEReference (BuildCellPort  (BuildCell "585324508_Cell" "" true)  (Build_Abstract_Port InputPortEClass  (BuildInputPort "1720339_Port" "" "b") ))) ::
		nil)
	).
