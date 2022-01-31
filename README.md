# CoqTL

CoqTL allows users to develop model transformation engines, write model transformations, and prove engine/transformation correctness in Coq. 

```
Definition Moore2Mealy :=
    transformation
    [
      rule "state"
      from [Moore.StateClass]
      to [
        elem "s"
          (fun _ _ s => BuildState (Moore.State_getName s)) nil
      ];
      rule "transition"
      from [Moore.TransitionClass]
      to [
        elem "t"
          (fun _ m t => BuildTransition 
                          (Moore.Transition_getInput t)
                          (value (option_map Moore.State_getOutput (Moore.Transition_getTarget t m))))
          [
            link
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionSource mealy_tr
                  (maybeResolve tls m "s" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getSourceObject moore_tr m))));
            link 
              (fun tls _ m moore_tr mealy_tr =>
                maybeBuildTransitionTarget mealy_tr
                  (maybeResolve tls m "s" Mealy.StateClass 
                    (maybeSingleton (Moore.Transition_getTargetObject moore_tr m))))
          ]
      ]
].
```

## Organization of the repository 

* Folder [core](https://github.com/atlanmod/coqtl/tree/master/core) - contains the source files for CoqTL engine.
* Folder [transformations](https://github.com/atlanmod/coqtl/tree/master/transformations) - contains sample CoqTL transformations and their proofs.
* Folder [libs](https://github.com/atlanmod/coqtl/tree/master/libs) - contains a code generator to translate `xmi` and `ecore` files into Coq. While not necessary to run CoqTL, the sources of the generator are in the [coqtl-model-import](https://github.com/atlanmod/coqtl-model-import) repository.
* Folder [.vscode](https://github.com/atlanmod/coqtl/tree/master/.vscode) - contains a task file for vscode user to `recompile`, `clean`, `execute code generator`.

## Installation

CoqTL requires a working installation of [Coq](https://coq.inria.fr/) (`coqc` and `coq_makefile` in the path). It is tested under Coq 8.15.0.

To install CoqTL:
```
git clone https://github.com/atlanmod/coqtl.git
cd coqtl
. compile.sh
```

## Publications

Here are the publications describing CoqTL and the pointer to the version of CoqTL they refer to. 

* Massimo Tisi, Zheng Cheng. CoqTL: an Internal DSL for Model Transformation in Coq. ICMT'2018. [[pdf]](https://hal.inria.fr/hal-01828344/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Rémi Douence. CoqTL: A Coq DSL for Rule-Based Model Transformation. SOSYM'2019. [[pdf]](https://hal.archives-ouvertes.fr/hal-02333564/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Joachim Hotonnier. Certifying a Rule-Based Model Transformation Engine for Proof Preservation. MODELS'2020. [[pdf]](https://hal.inria.fr/hal-02907622/document) [[git]](https://github.com/atlanmod/CoqTL/tree/2a8cea5)
* Zheng Cheng, Massimo Tisi. Deep Specification and Proof Preservation for the CoqTL Transformation Language. [[git]](https://github.com/atlanmod/CoqTL/tree/948eb94)

## Questions and discussion

If you experience issues installing or using CoqTL, you can submit an issue on [github](https://github.com/atlanmod/coqtl/issues) or contact us at:

* Massimo Tisi: massimo.tisi@imt-atlantique.fr
* Zheng Cheng: zheng.cheng@inria.fr

## License

CoqTL itself is licensed under Eclipse Public License (v2). See LICENSE.md in the root directory for details. Third party libraries are under independent licenses, see their source files for details.
