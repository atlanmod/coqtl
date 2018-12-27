CoqTL: an Internal DSL for Model Transformation in Coq
=======
In model-driven engineering, model transformation (MT) verification is essential for reliably producing software artifacts. While recent advancements have enabled automatic Hoare-style verification for non-trivial MTs, there are certain verification tasks (e.g. induction) that are intrinsically difficult to automate. Existing tools that aim at simplifying the interactive verification of MTs typically translate the MT specification (e.g. in ATL) and properties to prove (e.g. in OCL) into an interactive theorem prover. However, since the MT specification and proof phases happen in separate languages, the proof developer needs a deep knowledge of the translation logic. Naturally any error in the MT translation could cause unsound verification, i.e. the MT executed in the original environment may have different semantics from the verified MT.

We propose an alternative solution by designing and implementing an internal domain specific language, namely CoqTL, for the specification of declarative MTs directly in the Coq interactive theorem prover.  Expressions in CoqTL are written in Gallina (the specification language of Coq), increasing the possibilities of reuse of native Coq libraries in the transformation definition and proof. In this repository, it contains the example and proofs of CoqTL.

Usage
------
* To compile CoqTL libraries and sample transformations:
> coq_makefile -f _CoqProject -o Makefile

> make

* Sample usage e.g.:
> Run model transformation: examples/Class2Relational/PersonTest.v

> Proofs: examples/Class2Relational/theorems/thm_c2r_complete.v

Contacts
------
> Massimo Tisi: massimo.tisi@imt-atlantique.fr

> Zheng Cheng: zheng.cheng@imt-atlantique.fr