This sub-directory contains the example Class2Relational transformation.

Structure
------

* The CoqTL program for this transformation is contained in the root directory, including involved metamodels, and user transformation.
* The CoqTL proofs for this transformation is contained in the **Theorems** directory.
  * The proofs with `_impl` suffix are proved along with the engine implementation, and hence might be broken when engine updated.
  * The proofs with `_spec` suffix are proved along with the engine specification, and hence are more resilent to engine updates.
  * Details can be found in the reference corresponding to this case study [(ref)]().
* The same transformation expressed in ATL+EMF is contained in the **resource** directory for reference.

Reproduce
------
To reproduce the result provided in [(ref)](), users can show that by updating engine implementation, the proofs with `_spec` suffix remains unchanged of proof steps:

0. Make sure `Class2Relational.v` and a proof of interest (`_spec` suffix) import the same engine implementation, e.g. `core.Semantics`.
1. [Compile CoqTL]().
2. Open the proof of interest, and go through the proof steps to understand (optional).
3. Update `Class2Relational.v` and the proof of interest to import the same **new** engine implementation, e.g. `core.Semantics_v2`.
3. Re-[Compile CoqTL]().
4. Open the proof of interest, and go through the proof steps without any changes. Witness that the proof efforts are preserved when engine behaviors are changed.

Metrics
------

To generate metrics provided in [(ref)](), using the following calculation under the same path of this README file:

```
coqwc *.v
```

