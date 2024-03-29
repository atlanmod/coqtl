# CoqTL

CoqTL is an internal language in Coq, for writing rule-based model- and graph- transformations. The language is associated with a library to simplify proving transformation correctness in Coq. 

For instance, the following CoqTL code transforms [Moore machines](https://en.wikipedia.org/wiki/Moore_machine) into [Mealy machines](https://en.wikipedia.org/wiki/Mealy_machine) (if we disregard the first output symbol of the Moore machine). The full transformation, including type annotations, is available [here](./transformations/Moore2Mealy/Moore2Mealy.v).

```coq
Definition Moore2Mealy :=
  transformation
  [
    rule "state"
    from [Moore.StateClass]
    to [
      elem "s'"
        (fun _ _ s => BuildState (Moore.State_getName s)) nil
    ];
    
    rule "transition"
    from [Moore.TransitionClass]
    to [
      elem "t'"
        (fun _ m t => 
          BuildTransition 
            (Moore.Transition_getInput t)
            (value (option_map Moore.State_getOutput (Moore.Transition_getTarget t m))))
        [
          link
            (fun tls _ m tr tr' =>
              maybeBuildTransitionSource tr'
                (maybeResolve tls m "s'" Mealy.StateClass 
                  (maybeSingleton (Moore.Transition_getSourceObject tr m))));
          link 
            (fun tls _ m tr tr' =>
              maybeBuildTransitionTarget tr'
                (maybeResolve tls m "s'" Mealy.StateClass 
                  (maybeSingleton (Moore.Transition_getTargetObject tr m))))
        ]
  ]
].
```

## Organization of the repository 

* [core/](https://github.com/atlanmod/coqtl/tree/master/core) - source files of the CoqTL engine.
* [transformations/](https://github.com/atlanmod/coqtl/tree/master/transformations) - sample CoqTL transformations and associated proofs.
* [libs/](https://github.com/atlanmod/coqtl/tree/master/libs) - an importer that translates `ecore` metamodels and `xmi` models into Coq. While not necessary to run CoqTL, the sources of the importer are in the [coqtl-model-import](https://github.com/atlanmod/coqtl-model-import) repository.
* [.vscode/](https://github.com/atlanmod/coqtl/tree/master/.vscode) - convenience tasks for vscode: `make`, `clean`, `ecore2v`,  `xmi2v`.

## Installation

CoqTL requires a working installation of [Coq](https://coq.inria.fr/) (`coqc` and `coq_makefile` in the path). It is tested under Coq 8.15.0.

To install CoqTL:
```
git clone https://github.com/atlanmod/coqtl.git
cd coqtl
./compile.sh
```

### Alternative installation using Visual Studio Code remote container

Instead of installing coq directly on your machine you can use Visual Studio Code with the development container configuration we provide.

When opening the project with Visual Studio Code the editor will ask you to install the [Remote - Containers](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) extension to use the feature. Be sure to read the "Install" section of the [remote containers extension](https://marketplace.visualstudio.com/items?itemName=ms-vscode-remote.remote-containers) to correctly install and setup docker on your machine.

Then, once the remote container extension is installed and docker setup, Visual Studio Code will inform you that the current workspace can be opened in a container. Click "Reopen in Container" to start building the container. Be patient, docker will first download the image which can take some time depending on your internet connection. The image only to need to be built once, next launches are faster.


Coq theories can be found in `/home/vscode/.opam/default/lib/coq/theories`. One can add this folder to its workspace by right clicking in the exporer panel and selecting "Add folder to workspace".

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
