# Generic program analyses for D

Rocq formalization of Exercises 1 and 2 in [the solution](doc/project1/project1_solution.tex):
transitional analysis and a definitional interpreter.
Both analyses and their soundness proofs take an `AbstractDomain` record containing the
abstract memory CPO, abstract union, Galois connection, whole-memory transfers, and their
monotonicity and soundness proofs. The implementation uses the Rocq standard
library.

`repeat C E` has do-while semantics: enter `C`, then test `E` in the
resulting memory; a nonzero result repeats the body. `label` gives a command's
entry point, so `label (CRepeat l body e) = label body`. `node_label` gives
the unique attached label; for a repeat, it identifies the test after the body.
Lookup and computed goto use node labels. Both public interpreters start at
command entry points and use auxiliary node interpreters for the tests.

The lecture notes in [`doc/lecture slide/`](doc/lecture%20slide/) are from
[Kwangkeun Yi's Program Analysis course](https://kwangkeunyi.snu.ac.kr/4541.664A/26/).

## Dependencies

- Rocq 9.0.1 and Rocq Standard Library 9.0.0 (`rocq-core` and `rocq-stdlib` in opam).
- Coq compatibility binaries 9.0.1 (`coq-core` in opam), used by the Makefile.
- GNU Make and a Unix shell with standard utilities, including `find`, `sort`, and `cmp`.

For an existing opam switch, install the tested Rocq packages with:

```sh
opam install rocq-core.9.0.1 rocq-stdlib.9.0.0 coq-core.9.0.1
eval "$(opam env)"
```

The build uses `rocq` and `coq_makefile`; `make audit` also uses `coqtop` and
`coqchk`. These commands must be on `PATH`. All proof imports come from the
standard library or this repository; no additional Rocq libraries are required.

## Build

Verified with Rocq 9.0.1, Standard Library 9.0.0, OCaml 5.4.1, and GNU Make 4.4.1:

```sh
make          # all definitions, proofs, and examples
make core     # definitions and generic proofs
make audit    # Print Assumptions and independent kernel checking
make clean
```

## Sources

| Directory | Contents |
| --- | --- |
| `src/Foundations/` | Predicate sets, CPOs, least fixed points, and the Kleene theorem. |
| `src/Language/` | Syntax, concrete transitions, and the collecting interpreter. |
| `src/Abstract/` | The shared domain record, both abstract analyses, and soundness. |
| `src/Examples/` | One-element and nonlattice domain instances, proved semantic examples, and the assumptions audit. |

The construction needs no classical axioms, finite height, or widening. All
audited results are closed under the global context, with no admitted proofs.
Concrete watermark domains and convergence algorithms remain future work.

## Definition and theorem locations

| Part | Declaration | File and line |
| --- | --- | --- |
| Program syntax | `Program` | [src/Language/Syntax.v:41](src/Language/Syntax.v#L41) |
| Exercise 1: collecting semantics | `Reach` | [src/Language/Semantics.v:94](src/Language/Semantics.v#L94) |
| Exercise 1: abstract semantics | `Reach_sharp` | [src/Abstract/Transition.v:114](src/Abstract/Transition.v#L114) |
| Exercise 1: soundness theorem | `reachability_sound` | [src/Abstract/TransitionSound.v:68](src/Abstract/TransitionSound.v#L68) |
| Exercise 2: collecting interpreter | `outputs` | [src/Language/Interpreter.v:42](src/Language/Interpreter.v#L42) |
| Exercise 2: abstract interpreter | `outputs_sharp` | [src/Abstract/Interpreter.v:35](src/Abstract/Interpreter.v#L35) |
| Exercise 2: interpreter soundness theorem | `outputs_sound` | [src/Abstract/InterpreterSound.v:69](src/Abstract/InterpreterSound.v#L69) |
