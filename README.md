# Generic transitional analysis for D

Rocq formalization of Exercise 1 in [the solution](doc/project1/project1_solution.tex).
The analysis and soundness proofs take an `AbstractDomain` record containing the
abstract memory CPO, abstract union, Galois connection, whole-memory transfers, and their
monotonicity and soundness proofs. The implementation uses the Rocq standard
library; it has no ConCRIS dependency.

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
| `src/Language/` | Syntax and concrete semantics. |
| `src/Abstract/` | The domain record, abstract transitions, and soundness. |
| `src/Examples/` | One-element and nonlattice domain instances, proved semantic examples, and the assumptions audit. |

The construction needs no classical axioms, finite height, or widening. All
audited results are closed under the global context, with no admitted proofs.
The current scope is transitional semantics and its generic proof; concrete
watermark domains and convergence algorithms remain future work.

