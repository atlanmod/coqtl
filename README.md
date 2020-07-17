CoqTL: an Internal DSL for Model Transformation in Coq
=======
Executable engines for relational model-transformation languages evolve continuously because of language extension, performance improvement and bug fixes. While new versions generally change the engine semantics, end-users expect to get backward-compatibility guarantees, so that existing transformations do not need to be adapted at every engine update.

The CoqTL model-transformation language allows users to define model transformations, theorems on their behavior and machine-checked proofs of these theorems in Coq. Backward-compatibility for CoqTL involves also the preservation of these proofs. However, proof preservation is challenging, as proofs are easily broken even by small refactorings of the code they verify.

In this paper we present the solution we designed for the evolution of CoqTL, and by extension, of rule-based transformation engines. We provide a deep specification of the transformation engine, including a set of theorems that must hold against the engine implementation. Then, at each milestone in the engine development, we certify the new version of the engine against this specification, by providing proofs of the impacted theorems. The certification formally guarantees end-users that all the proofs they write using the provided theorems will be preserved through engine updates.

We illustrate the structure of the deep specification theorems, we produce a machine-checked certification of three versions of CoqTL against it, and we show examples of user theorems that leverage this specification and are thus preserved through the updates.

Repository structure
------
* The CoqTL language and its examples are contained by [fr.inria.atlanmod.coqtl.coq](/fr.inria.atlanmod.coqtl.coq/)
  * language aspect is contained by [core](/fr.inria.atlanmod.coqtl.coq/core/), which modularized into:
    * Specification
      * [CoqTL engine specification](/fr.inria.atlanmod.coqtl.coq/core/Engine.v)
      * [CoqTL engine derived specification](/fr.inria.atlanmod.coqtl.coq/core/EngineProofs.v)
      * [Metamodel interface](/fr.inria.atlanmod.coqtl.coq/core/Metamodel.v)
      * [Model interface](/fr.inria.atlanmod.coqtl.coq/core/Model.v)
    * Implementation
      * [Abstract Syntax](/fr.inria.atlanmod.coqtl.coq/core/Syntax.v)
      * Semantic functions [(v1)](/fr.inria.atlanmod.coqtl.coq/core/Semantics.v) [(v2)](/fr.inria.atlanmod.coqtl.coq/core/Semantics_v2.v) [(v3)](/fr.inria.atlanmod.coqtl.coq/core/Semantics_v3.v)
      * [Expression Evaluation](/fr.inria.atlanmod.coqtl.coq/core/Expressions.v)
    * Certification 
      * Implementation against specification [(v1)](/fr.inria.atlanmod.coqtl.coq/core/Certification.v) [(v2)](/fr.inria.atlanmod.coqtl.coq/core/Certification_v2.v) [(v3)](/fr.inria.atlanmod.coqtl.coq/core/Certification_v3.v)
  * examples is contained by [examples](/fr.inria.atlanmod.coqtl.coq/examples/):
    * [Class2Relational](/fr.inria.atlanmod.coqtl.coq/examples/Class2Relational/)
    * [HSM2FSM](/fr.inria.atlanmod.coqtl.coq/examples/HSM2FSM)
* The code generator from EMF metamodel/model to CoqTL is contained by [fr.inria.atlanmod.coqtl.generators](/fr.inria.atlanmod.coqtl.generators/) (experimental).

Compilation
------
See [compilation](https://github.com/atlanmod/CoqTL/wiki/Compiling-CoqTL) on the wiki.

Issues
------
If you experience issues installing or using CoqTL, you can submit an issue on [github](https://github.com/atlanmod/CoqTL/issues) or contact us at:

> Massimo Tisi: massimo.tisi@imt-atlantique.fr

> Zheng Cheng: zheng.cheng@inria.fr

License
------
CoqTL itself is licensed under Eclipse Public License (v2). See LICENSE.md in the root directory for details. Third party libraries are under independent licenses, see their source files for details.