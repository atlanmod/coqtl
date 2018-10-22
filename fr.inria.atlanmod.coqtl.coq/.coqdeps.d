core/utils/tArith.vo core/utils/tArith.glob core/utils/tArith.v.beautified: core/utils/tArith.v core/utils/tNotation.vo
core/utils/tArith.vio: core/utils/tArith.v core/utils/tNotation.vio
core/utils/tList.vo core/utils/tList.glob core/utils/tList.v.beautified: core/utils/tList.v
core/utils/tList.vio: core/utils/tList.v
core/utils/tConcat.vo core/utils/tConcat.glob core/utils/tConcat.v.beautified: core/utils/tConcat.v core/utils/tList.vo
core/utils/tConcat.vio: core/utils/tConcat.v core/utils/tList.vio
core/utils/tTuple.vo core/utils/tTuple.glob core/utils/tTuple.v.beautified: core/utils/tTuple.v
core/utils/tTuple.vio: core/utils/tTuple.v
core/utils/tString.vo core/utils/tString.glob core/utils/tString.v.beautified: core/utils/tString.v
core/utils/tString.vio: core/utils/tString.v
core/utils/tPrint.vo core/utils/tPrint.glob core/utils/tPrint.v.beautified: core/utils/tPrint.v
core/utils/tPrint.vio: core/utils/tPrint.v
core/utils/tNotation.vo core/utils/tNotation.glob core/utils/tNotation.v.beautified: core/utils/tNotation.v
core/utils/tNotation.vio: core/utils/tNotation.v
core/utils/tPair.vo core/utils/tPair.glob core/utils/tPair.v.beautified: core/utils/tPair.v
core/utils/tPair.vio: core/utils/tPair.v
core/utils/tTop.vo core/utils/tTop.glob core/utils/tTop.v.beautified: core/utils/tTop.v core/utils/tArith.vo core/utils/tList.vo core/utils/tTuple.vo core/utils/tConcat.vo core/utils/tNotation.vo core/utils/tString.vo core/utils/tPrint.vo core/utils/tPair.vo
core/utils/tTop.vio: core/utils/tTop.v core/utils/tArith.vio core/utils/tList.vio core/utils/tTuple.vio core/utils/tConcat.vio core/utils/tNotation.vio core/utils/tString.vio core/utils/tPrint.vio core/utils/tPair.vio
core/utils/CpdtTactics.vo core/utils/CpdtTactics.glob core/utils/CpdtTactics.v.beautified: core/utils/CpdtTactics.v
core/utils/CpdtTactics.vio: core/utils/CpdtTactics.v
core/Object.vo core/Object.glob core/Object.v.beautified: core/Object.v
core/Object.vio: core/Object.v
core/Model.vo core/Model.glob core/Model.v.beautified: core/Model.v
core/Model.vio: core/Model.v
core/Typing.vo core/Typing.glob core/Typing.v.beautified: core/Typing.v
core/Typing.vio: core/Typing.v
core/Decidability.vo core/Decidability.glob core/Decidability.v.beautified: core/Decidability.v
core/Decidability.vio: core/Decidability.v
core/Metamodel.vo core/Metamodel.glob core/Metamodel.v.beautified: core/Metamodel.v core/Typing.vo core/Decidability.vo core/Object.vo
core/Metamodel.vio: core/Metamodel.v core/Typing.vio core/Decidability.vio core/Object.vio
core/Iterator.vo core/Iterator.glob core/Iterator.v.beautified: core/Iterator.v core/Typing.vo core/Decidability.vo
core/Iterator.vio: core/Iterator.v core/Typing.vio core/Decidability.vio
core/DefaultIterator.vo core/DefaultIterator.glob core/DefaultIterator.v.beautified: core/DefaultIterator.v core/utils/tTop.vo core/Iterator.vo core/utils/CpdtTactics.vo
core/DefaultIterator.vio: core/DefaultIterator.v core/utils/tTop.vio core/Iterator.vio core/utils/CpdtTactics.vio
core/Engine.vo core/Engine.glob core/Engine.v.beautified: core/Engine.v core/utils/tTop.vo core/Model.vo
core/Engine.vio: core/Engine.v core/utils/tTop.vio core/Model.vio
core/CoqTL.vo core/CoqTL.glob core/CoqTL.v.beautified: core/CoqTL.v core/Metamodel.vo core/Model.vo core/Engine.vo core/Iterator.vo core/utils/tTop.vo core/utils/tArith.vo core/utils/CpdtTactics.vo
core/CoqTL.vio: core/CoqTL.v core/Metamodel.vio core/Model.vio core/Engine.vio core/Iterator.vio core/utils/tTop.vio core/utils/tArith.vio core/utils/CpdtTactics.vio
core/Notations.vo core/Notations.glob core/Notations.v.beautified: core/Notations.v core/CoqTL.vo core/DefaultIterator.vo
core/Notations.vio: core/Notations.v core/CoqTL.vio core/DefaultIterator.vio
examples/Graph2Tree/GraphMetamodel.vo examples/Graph2Tree/GraphMetamodel.glob examples/Graph2Tree/GraphMetamodel.v.beautified: examples/Graph2Tree/GraphMetamodel.v core/utils/tTop.vo core/Metamodel.vo core/Model.vo core/Object.vo
examples/Graph2Tree/GraphMetamodel.vio: examples/Graph2Tree/GraphMetamodel.v core/utils/tTop.vio core/Metamodel.vio core/Model.vio core/Object.vio
examples/Graph2Tree/GraphMetamodelPattern.vo examples/Graph2Tree/GraphMetamodelPattern.glob examples/Graph2Tree/GraphMetamodelPattern.v.beautified: examples/Graph2Tree/GraphMetamodelPattern.v examples/Graph2Tree/GraphMetamodel.vo
examples/Graph2Tree/GraphMetamodelPattern.vio: examples/Graph2Tree/GraphMetamodelPattern.v examples/Graph2Tree/GraphMetamodel.vio
examples/Graph2Tree/GraphModel.vo examples/Graph2Tree/GraphModel.glob examples/Graph2Tree/GraphModel.v.beautified: examples/Graph2Tree/GraphModel.v core/Model.vo examples/Graph2Tree/GraphMetamodel.vo
examples/Graph2Tree/GraphModel.vio: examples/Graph2Tree/GraphModel.v core/Model.vio examples/Graph2Tree/GraphMetamodel.vio
examples/Graph2Tree/GraphModel2.vo examples/Graph2Tree/GraphModel2.glob examples/Graph2Tree/GraphModel2.v.beautified: examples/Graph2Tree/GraphModel2.v core/Model.vo examples/Graph2Tree/GraphMetamodel.vo
examples/Graph2Tree/GraphModel2.vio: examples/Graph2Tree/GraphModel2.v core/Model.vio examples/Graph2Tree/GraphMetamodel.vio
examples/Graph2Tree/Graph2TreeIterator.vo examples/Graph2Tree/Graph2TreeIterator.glob examples/Graph2Tree/Graph2TreeIterator.v.beautified: examples/Graph2Tree/Graph2TreeIterator.v core/utils/tTop.vo core/Iterator.vo core/utils/CpdtTactics.vo examples/Graph2Tree/GraphMetamodel.vo
examples/Graph2Tree/Graph2TreeIterator.vio: examples/Graph2Tree/Graph2TreeIterator.v core/utils/tTop.vio core/Iterator.vio core/utils/CpdtTactics.vio examples/Graph2Tree/GraphMetamodel.vio
examples/Graph2Tree/Graph2Tree.vo examples/Graph2Tree/Graph2Tree.glob examples/Graph2Tree/Graph2Tree.v.beautified: examples/Graph2Tree/Graph2Tree.v core/utils/tTop.vo core/Notations.vo core/Model.vo core/CoqTL.vo examples/Graph2Tree/GraphMetamodel.vo examples/Graph2Tree/GraphMetamodelPattern.vo examples/Graph2Tree/GraphModel.vo examples/Graph2Tree/GraphModel2.vo examples/Graph2Tree/Graph2TreeIterator.vo
examples/Graph2Tree/Graph2Tree.vio: examples/Graph2Tree/Graph2Tree.v core/utils/tTop.vio core/Notations.vio core/Model.vio core/CoqTL.vio examples/Graph2Tree/GraphMetamodel.vio examples/Graph2Tree/GraphMetamodelPattern.vio examples/Graph2Tree/GraphModel.vio examples/Graph2Tree/GraphModel2.vio examples/Graph2Tree/Graph2TreeIterator.vio
examples/Graph2Tree/Graph2TreeNoIter.vo examples/Graph2Tree/Graph2TreeNoIter.glob examples/Graph2Tree/Graph2TreeNoIter.v.beautified: examples/Graph2Tree/Graph2TreeNoIter.v core/utils/tTop.vo core/Notations.vo core/Model.vo core/CoqTL.vo core/DefaultIterator.vo examples/Graph2Tree/GraphMetamodel.vo examples/Graph2Tree/GraphMetamodelPattern.vo examples/Graph2Tree/GraphModel.vo examples/Graph2Tree/GraphModel2.vo
examples/Graph2Tree/Graph2TreeNoIter.vio: examples/Graph2Tree/Graph2TreeNoIter.v core/utils/tTop.vio core/Notations.vio core/Model.vio core/CoqTL.vio core/DefaultIterator.vio examples/Graph2Tree/GraphMetamodel.vio examples/Graph2Tree/GraphMetamodelPattern.vio examples/Graph2Tree/GraphModel.vio examples/Graph2Tree/GraphModel2.vio
