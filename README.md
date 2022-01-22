# CoqTL

CoqTL allows users to write model transformations, specify and prove theorems on their behavior in Coq. 

## Organization of the repository 

* Folder [core](https://github.com/atlanmod/coqtl/tree/master/core) - contains the source files for CoqTL engine.
* Folder [transformations](https://github.com/atlanmod/coqtl/tree/master/transformations) - contains sample CoqTL transformations and their proofs.
* Folder [libs](https://github.com/atlanmod/coqtl/tree/master/libs) - contains a code generator to translate `xmi` and `ecore` files into Coq.
* Folder [.vscode](https://github.com/atlanmod/coqtl/tree/master/.vscode) - contains a task file for vscode user to `recompile`, `clean`, `execute code generator`.

## Installation

CoqTL installation is tested under:
* Ubuntu 18.04 and Windows 10 (ensure `make` is installed)
* coq 8.14.0

To install CoqTL:
```
git clone https://github.com/atlanmod/coqtl.git
cd coqtl
. compile.sh
```

## CoqTL History

The `master` branch host the latest stable version of CoqTL. For earlier versions, please consult the following papers and commits for more information:
* Massimo Tisi, Zheng Cheng. CoqTL: an Internal DSL for Model Transformation in Coq. ICMT'2018. [[pdf]](https://hal.inria.fr/hal-01828344/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Rémi Douence. CoqTL: A Coq DSL for Rule-Based Model Transformation. SOSYM'2019. [[pdf]](https://hal.archives-ouvertes.fr/hal-02333564/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Joachim Hotonnier. Certifying a Rule-Based Model Transformation Engine for Proof Preservation. MODELS'2020. [[pdf]](https://hal.inria.fr/hal-02907622/document) [[git]](https://github.com/atlanmod/CoqTL/tree/2a8cea5)
* Zheng Cheng, Massimo Tisi. Deep Specification and Proof Preservation for the CoqTL Transformation Language. [[git]](https://github.com/atlanmod/CoqTL/tree/948eb94)

## Questions and discussion

If you experience issues installing or using CoqTL, you can submit an issue on [github](https://github.com/atlanmod/coqtl/issues) or contact us at:

> Massimo Tisi: massimo.tisi@imt-atlantique.fr

> Zheng Cheng: zheng.cheng@inria.fr

## License

CoqTL itself is licensed under Eclipse Public License (v2). See LICENSE.md in the root directory for details. Third party libraries are under independent licenses, see their source files for details.
