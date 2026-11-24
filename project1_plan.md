# Project 1 plan: generic abstract interpretation for D

Prepared: 2026-11-20  
Deadline stated in project1.pdf: November 25, in class.

Rocq implementation structure added: 2026-11-23.

## 1. Objective and scope

Formalize the transitional analysis in [project1_solution.tex](doc/project1/project1_solution.tex) as a generic program analyzer in Rocq, covering Exercise 1 in [project1.pdf](doc/project1/project1.pdf): concrete collecting semantics, a generic abstract transition system, and local-to-global reachability soundness.

The current assignment explicitly allows all abstract domains to remain parameters connected to concrete powersets by Galois connections. Package the abstract memory domain, its auxiliary operations, and their proof obligations in an `AbstractDomain` record, and parameterize the analyzer and its proofs by a value of that record. Section 10 specifies the Rocq files and their interfaces. A parser, production congruence or relational domains, and the final watercheck tool remain deferred.

Use [project.pdf](doc/project.pdf) for the complete syntax and the eventual watermark objective. Treat the requirements in project1.pdf as authoritative for this submission.

## 2. Reading map

Page references below mean PDF pages, not printed lecture slide numbers.

| Source | Relevant material | Planned use |
| --- | --- | --- |
| project1.pdf, pp. 1–3 | Exercise 1 and its proof obligation | Submission checklist for transitional semantics |
| project.pdf, p. 2 | D syntax, addresses, readInt, computed goto | Complete constructor inventory |
| project.pdf, pp. 2–3 | P1/P2 and watermark example; AI verification requirement | Future compatibility and verification record |
| lecture slide/slide8.pdf, pp. 5–9, 17–22, 33–35 | Reachability fixed point, label maps, partitioning and joining | Exercise 1 framework |
| lecture slide/slide8.pdf, pp. 38–44 | Concrete/abstract transition example and operator soundness | Rule and proof templates, extended for D |
| lecture slide/slide3-0.pdf, pp. 1–8 | Transitional collecting semantics | Short cross-check of reachability definitions |
| lecture slide/slide5.pdf, p. 6 | Fixpoint transfer theorem | Soundness proof architecture |
| lecture slide/slide2.pdf | Semantic domains, continuity, recursive equations | Existence of collecting-semantics fixed points |

Use the slides as templates and check their equations against the language conventions below.

## 3. Settle the semantic conventions first

Write a short conventions section before defining the semantics. Distinguish source requirements from assumptions where the sources leave behavior unspecified.

- **Program representation:** fix one whole program P. Every Cmd node, including sequence, if, and repeat, has its own natural-number label. Build a label-to-node table and parent/context information. Numeric labels need not follow source order.
- **Values and memory (user revision):** use `Var := string`, values `Z`, an injective address map `addr : string -> Z`, and `Memory := Z -> Z`. Then `x` reads `m (addr x)`, `&x` evaluates to `addr x`, and `*x` reads `m (m (addr x))`. Every integer address is a valid memory cell, including addresses not assigned to a variable name. Variable and address spaces need no finite enumeration. State initialization assumptions through M0 rather than silently setting all cells to zero. This supersedes the finite-variable memory convention in the written solution.
- **Input:** readInt nondeterministically returns any integer on every evaluation. There is no input stream in the required state L × M. Treat repeated occurrences as independent choices.
- **Truth:** use zero for false, nonzero for true; E1 < E2 produces 0 or 1.
- **Missing jump targets:** a goto result that is not an existing source label has no successor. Memory access is total on integer addresses, so dereference and store have no invalid-address case.
- **Termination:** introduce a fresh terminal point halt, outside the numeric source-label set, with no outgoing transition. Source goto targets only existing Cmd labels.
- **Loop convention (user-specified):** interpret repeat C E exactly as while E C. Test E before each iteration; nonzero enters C and zero exits. Normal completion of C returns to the repeat command label.
- **Entry and interior jumps:** entering a labeled structured command starts it normally. Jumping into its interior uses that node's lexical continuation in P. It does not create a return to the goto site.

### Repeat control flow

The original repeat label is the test point, so no synthetic loop labels are needed. For l : repeat C E with normal continuation k, define nextTrue(l) = label(C), nextFalse(l) = k, and give C the normal continuation l. A goto to l evaluates E before entering the body.

## 4. Shared semantic operators and types

Define expression evaluation relationally or as Eval_E : M → P(V), then take natural powerset extensions. Preserve the relation between an input memory and its evaluated values.

Prepare a table with concrete type, abstract type, and soundness assumption for every operator actually used. A compact generic interface is:

| Operator | Concrete type | Abstract type |
| --- | --- | --- |
| Expression evaluation | eval_E : P(M) → P(V) | eval_E# : M# → V# |
| Direct assignment | assign_x,E : P(M) → P(M) | assign_x,E# : M# → M# |
| Indirect assignment | store_x,E : P(M) → P(M) | store_x,E# : M# → M# |
| Guard selection | assume_E,b : P(M) → P(M) | assume_E,b# : M# → M# |
| Target selection | target_E,k : P(M) → P(M) | target_E,k# : M# → M# |
| Memory union | union : P(M) × P(M) → P(M) | union_sharp : M# × M# → M#, derived from bundled indexed abstract union |
| Identity | id : P(M) → P(M) | id# : M# → M# |

The expression-evaluation row is an optional extension. Following the solution, the initial Rocq implementation uses whole-memory assignment, store, guard, and target operations and therefore does not require a separate abstract value domain.

For example:

- assign_x,E(X) = {m[addr(x) ↦ v] | m ∈ X, v ∈ Eval_E(m)}.
- store_x,E(X) = {m[m(addr(x)) ↦ v] | m ∈ X, v ∈ Eval_E(m)}.
- assume_E,true(X) = {m ∈ X | some v ∈ Eval_E(m) is nonzero}; false selects a possible zero.
- target_E,k(X) = {m ∈ X | k ∈ Eval_E(m)}.

Define Eval for every expression constructor: n, addition, multiplication, negation, comparison, x, *x, &x, and readInt. Arithmetic combines possible operand values within the same memory. Dereference reads the integer address stored in the named pointer cell; it requires no inverse mapping from addresses to variable names.

Using whole-command transfer operators as primitives keeps the abstract memory domain fully generic and permits relational domains later. If the final exposition decomposes them into lookup, dereference, arithmetic, and update operators, add the corresponding types and proof obligations; do not leave those interfaces implicit.

**Exactness checkpoint:** independently computing eval_E(X) and crossing it with every memory in X can introduce values from unrelated memories. That may be a sound abstraction, but is not the exact natural powerset collecting semantics.

Assume a Galois connection P(M) ⇄ M# and any additional required connections, such as P(V) ⇄ V#. For each unary memory transfer T require:

T(γ_M(a)) ⊆ γ_M(T#(a)).

State monotonicity and the continuity assumptions needed by the chosen fixed-point construction explicitly. Soundness and a Galois connection alone do not imply continuity or finite convergence.

## 5. Exercise 1 work packages

### 5.1 Construct static control relations

Define a recursive traversal with an inherited normal continuation k.

- Sequence entry goes to its first child. The first child's normal continuation is the second child's label; the second inherits k.
- If entry selects the true/false child. Both children inherit k.
- Repeat tests E at its own label: true enters the body and false goes to k. The body's normal continuation is the repeat label.
- Assignments continue to k.
- Goto has no ordinary fall-through. Its actual target depends on evaluating E.
- The whole program's normal continuation is halt.

Provide a constructor table for next, nextTrue, and nextFalse, explicitly marking inapplicable entries. Separate the lexical continuation metadata from the executable next edge: assigning a fall-through edge to goto would be incorrect.

**Deliverable:** definitions plus one annotated nested example showing sequence, branch, repeat, and an interior jump.

### 5.2 Define concrete one-step rules

Use S = L × M, where L contains the original Cmd labels and halt. Give rules for every constructor; halt has no outgoing rule.

Assignment evaluates in the old memory; indirect assignment also resolves the target address in that same memory. A conditional/test produces a successor for every feasible result of its evaluation. Goto E transfers to each valid source label obtained from Eval_E(m), preserving m.

Define:

- I = {(entry(P), m) | m ∈ M0}.
- Step(X) = {s' | some s ∈ X satisfies s → s'}.
- F(X) = I ∪ Step(X).
- Reach(P, M0) = lfp F.

Explain why F is monotone and continuous, and why its least fixed point collects all finite execution prefixes, including states on diverging executions.

### 5.3 Define generic abstract propagation

Use A = L → M#, pointwise ordering and abstract union, and:

- α_S(X)(l) = α_M({m | (l,m) ∈ X}).
- γ_S(a) = {(l,m) | m ∈ γ_M(a(l))}.

There is a type discrepancy to resolve explicitly: project1.pdf p. 2 describes the abstract one-step relation over label maps, whereas slide8.pdf pp. 17 and 34 use local pairs (L × M#). The printed partition-and-join formula naturally uses the latter.

Present both layers:

1. A syntax-directed local abstract transition relation over (L × M#), using each abstract transfer.
2. Its aggregate Step# : A → A, joining all incoming contributions at each destination.

If retaining the handout's map-to-map relation notation, define its meaning in terms of these contributions; do not apply partitioning to a map-to-map relation without a typed bridge.

For goto, give a local abstract transition to each original label k with result target_E,k#(a(l)). This avoids assuming that V# itself supports target enumeration. Unknown targets may conservatively propagate to all original labels.

Set I# = α_S(I), F#(a) = I# union_sharp Step#(a), and Reach# = sup_n (F#)^n(bottom). This increasing-chain limit is sound under monotonicity; identifying it as a fixed point additionally requires continuity. Abstract union and its monotonicity and soundness laws belong to AbstractDomain, separately from the CPO. Do not assume γ_M(bottom) is empty unless justified by the chosen connection.

### 5.4 Prove soundness

Prove local transition coverage by cases on the concrete rule: every step from a represented source memory is covered by the corresponding abstract rule. The key cases are indirect store, nondeterministic guards, and computed goto.

Then show:

1. Step(γ_S(a)) ⊆ γ_S(Step#(a)).
2. F(γ_S(a)) ⊆ γ_S(F#(a)).
3. lfp F ⊆ γ_S(sup_n (F#)^n(bottom)).

For the final step, compare the finite concrete and abstract iterates, then take chain limits using monotone concretization. Concrete F is continuous, making its limit the least fixed point; abstract continuity is unnecessary for soundness. Retain the general pre-fixed invariant lemma as a separate result. Type-check the relation-level formula in the handout through the local-pair lifting before invoking it.

## 6. Deferred scope

Exercise 2, the definitional interpreter, is deferred. Its mathematical design remains in `doc/project1/project1_solution.tex`; it has no files or milestones in the current Rocq implementation plan.

## 7. Verification and AI-use record

The project overview requires recording how every AI-assisted step was checked. Keep a table in the eventual submission with columns: proposed result, source/derivation, independent check, correction/status. This planning document is AI-assisted; the checks below are planned checks, not completed proofs.

| Planned check | Failure it should catch |
| --- | --- |
| Inventory all 6 command forms and 9 expression forms | Missing a language feature |
| Hand-trace direct and aliased indirect assignments | Updating the wrong cell or evaluating after mutation |
| Compare x := x + 1 on two different input memories | Accidental cross-memory products |
| Trace readInt guards and readInt + readInt | Dropped nondeterministic outcomes |
| Trace repeat with constant true/false tests | Incorrect polarity, executing the body when the initial test is false, or failing to retest |
| Jump into/out of nested branches and loops | Accidental goto return or wrong lexical continuation |
| Use nonconsecutive labels and a computed target | Assuming source order determines numeric successors |
| Check arbitrary integer addresses, missing jump targets, and terminal behavior | Undocumented or inconsistent boundary semantics |
| Compare finite collecting iterations with finite execution prefixes | Collecting/transition mismatch |
| Check a reachable infinite loop | Omitting reachable states on nonterminating executions |
| Type-check every operator and lifting formula | Mixing memory sets, value sets, local pairs, and label maps |
| Check every local proof and its fixed-point assumptions | Treating experiments or local soundness as a global proof |

Small bounded traces can detect errors but cannot establish soundness for all D programs. The submission needs the case analysis and fixed-point arguments.

## 8. Work sequence before November 25

| Target | Work | Exit condition |
| --- | --- | --- |
| Nov. 20 | Requirements, conventions, domain/operator tables | Every ambiguity and assumption is visible |
| Nov. 21 | Static successors and concrete transitional semantics | All constructors covered; nested jump and repeat traces checked |
| Nov. 22 | Abstract transitions and Exercise 1 proof | Typed Step# and complete local-to-global argument |
| Nov. 23 | Rocq structure and abstract-domain record interface | File responsibilities, dependencies, and proof obligations specified |
| Nov. 24 | Transitional analysis proof and cross-checks | Local-to-global reachability soundness; AI verification record completed |
| Before Nov. 25 class | Build and requirement audit | Transitional implementation and proofs checked against Exercise 1 |

The solution draft is in `doc/project1/project1_solution.tex`. The Rocq implementation should follow the dependency order and completion checks in Section 10. Formatting/submission details beyond the stated deadline are not specified in the supplied PDFs.

## 9. Deferred watercheck implementation

After this assignment, instantiate the generic memory domain to support:

- P1: integer values congruent to 123 modulo 260401.
- P2: a relation between variables whose sum is always 123.
- Pointer aliasing, indirect stores, and computed jump targets.
- Convergence engineering, worklist scheduling, and possibly widening.

Watermark claims concern all reachable memories at a chosen program point. Distinguish command entry from command exit, especially when unrelated goto edges also reach the successor. Avoid claiming a watermark merely because a point is unreachable, or inferring that failure to prove a watermark establishes its absence.

## 10. Rocq project structure

The implementation is under `src/`, using the logical namespace `DAnalyzer` and `-R src DAnalyzer` in `_CoqProject`. The file responsibilities below describe the implemented structure. Keep definitions and their supporting lemmas together; place the main reachability soundness proof in a dedicated file.

### 10.1 Source layout

```text
_CoqProject
Makefile
README.md
src/
  Foundations/
    Sets.v
    Order.v
    Fixpoint.v
  Language/
    Syntax.v
    ControlFlow.v
    Semantics.v
  Abstract/
    Domain.v
    Transition.v
    TransitionSound.v
  Examples/
    TrivialDomain.v
    NonLatticeDomain.v
    Examples.v
    Assumptions.v
```

`Makefile` follows `../../rocq/FlowDown`: discover sources under `src/`, regenerate `_CoqProject` only when its contents change, and invoke `coq_makefile` to generate `Makefile.coq`. It exposes `make`, `make core`, `make audit`, and `make clean`. `_CoqProject` contains the warning options, namespace mapping, and discovered source files. Generated build files and compiled artifacts are ignored by Git. `README.md` records the verified toolchain, build commands, main theorem names, and current scope. The verified toolchain is Rocq 9.0.1 with OCaml 5.4.1.

### 10.2 Foundations and language files

| File | Definitions and proofs it owns |
| --- | --- |
| `Foundations/Sets.v` | `set A := A -> Prop`, subset, empty set, union, indexed union, relational image, and elementary inclusion lemmas. Sets are predicates, not finite lists. |
| `Foundations/Order.v` | A bundled `CPO` record with order laws, bottom, and suprema specified only on chains; monotonicity and pointwise CPOs for predicates and maps. Use mutual ordering as equivalence. Concrete chain limits use ordinary set union; abstract union is not part of this record. |
| `Foundations/Fixpoint.v` | Natural-number iteration and its chain limit `iteration_limit`; `lfp` by the lecture's Kleene construction, with fixed-point laws under monotonicity and omega continuity. Generic finite-iterate and limit simulation theorems require only monotonicity on the abstract side. No classical axioms or D-specific definitions. |
| `Language/Syntax.v` | Expressions with all nine constructors and labeled commands with all six constructors; `label`, command-occurrence traversal, expression/command variable traversal, and the well-formed `Program` record requiring distinct labels. Variables are fixed string identifiers (`Var := string`); source labels are `nat`, integer constants are `Z`, and `halt` is not a syntax constructor. |
| `Language/ControlFlow.v` | Finite valid-point enumeration `points P`; recursive `lookup_cmd` over syntax with an inherited continuation; lookup soundness, completeness, and continuation scope proofs; `command_at`, `cont`, and partial successor functions `next`, `nextTrue`, and `nextFalse`. Prove validity of successor points. |

`Entry P` is the subtype of labels occurring in the fixed whole program. Numeric points `Halt | At nat` are defined in `Syntax.v`. The metadata functions and `Reach_points` prove that execution stays within `points P`. `lookup_cmd c k l` searches the syntax tree directly, returning the command at `l` with its lexical continuation. Sequence, branch, and repeat cases pass the appropriate inherited continuation to each recursive call. `lookup P l` starts with `lookup_cmd (root P) Halt l`. Representing `Halt` separately prevents it from becoming an integer jump target.

Follow the transitional presentation in `project1_solution.tex`: compute static successor metadata from syntax, then define transitions by command cases. For `goto`, `next`, `nextTrue`, and `nextFalse` are undefined. Its concrete rule evaluates the target expression and requires the result to name a source label. The abstract rule ranges over valid labels and applies the corresponding `target_sharp`. These are relational rules; no action datatype or compiled list of control-flow edges is needed.

### 10.3 Concrete semantics and the abstract-domain interface

| File | Definitions and proofs it owns |
| --- | --- |
| `Language/Semantics.v` | A `Definitions` section containing `AddressMap`, `Memory := Z -> Z`, integer-address update, expression evaluation `eval`, its powerset extension `eval_set`, truth tests, exact memory transfers `assign`, `store`, `assume`, and `target`, the state type `point * Memory`, syntax-directed `step`, collecting `Step`, `F`, and `Reach`, and finite paths and reachability. A following `Lemmas` section contains memory update laws, including preservation of distinct named variables; expression equations; transfer monotonicity and preservation of arbitrary unions, including the empty union; validity of transition points; collecting monotonicity and continuity; the Kleene characterization; and equivalence with finite execution prefixes. Both sections group memory, evaluation, transfers, and transitions separately. All expression choices and pointer resolution use the same pre-update memory. |
| `Abstract/Domain.v` | The `AbstractDomain` record described below, plus binary abstract union, abstraction coverage, concretization monotonicity, and coverage of union contributions. This file imports `Language.Semantics` for concrete transfers; it has no dependency on abstract propagation or its soundness proof. |

Use one explicit record argument `D : AbstractDomain M` for a fixed `M : AddressMap`. Its bundled CPO supplies the abstract carrier `A`. The intended fields are:

| Field or field group | Type/obligation |
| --- | --- |
| `memory_cpo` | A `CPO`, exposing carrier `A`, order `le`, bottom, and chain suprema. |
| `unions_sharp` | `set A -> A`, separately bundled abstract union. Binary `union_sharp` is its two-element case. |
| `unions_monotone` | If every contribution in `X` has a greater contribution in `Y`, then `unions_sharp X` is below `unions_sharp Y`. |
| `unions_sound` | Each contribution's concretization is included in the concretization of its abstract union. No order upper-bound or leastness law is required. |
| `alpha`, `gamma` | `alpha : set Memory -> A` and `gamma : A -> set Memory`. |
| `galois` | For every `X` and `a`, `le (alpha X) a <-> subset X (gamma a)`. |
| `assign_sharp` | `Var -> expr -> A -> A`. |
| `store_sharp` | `Var -> expr -> A -> A`. |
| `assume_sharp` | `expr -> bool -> A -> A`, with `true` selecting nonzero results. |
| `target_sharp` | `expr -> nat -> A -> A`, testing the integer denoted by a source label. |
| Transfer monotonicity | One proof for each operation, pointwise in its syntax parameters. |
| Transfer soundness | One proof for each operation: `T (gamma a)` is included in `gamma (T_sharp a)`. |

Store these data and proofs in the record rather than declaring unrelated global `Parameter`s or assuming global soundness axioms. Analyzer sections take `P` and `D` explicitly; adding a domain instance should require no changes to analyzer definitions or proofs. The local abstract transition rules use the bundled transfers directly, and their results are combined using the bundled abstract union. Abstract identity is the actual identity function.

No field assumes that `gamma bottom` is empty, that gamma preserves joins, or that abstract memories have a variable-wise product representation. A separate abstract value domain is unnecessary for these whole-memory transfers; add a separate optional interface if expression analysis later needs one. Keep chain limits, abstract union, and `alpha` in the semantic interface. Define abstract reachability from a supplied abstract input `a0` and derive the `a0 = alpha M0` corollary.

### 10.4 Abstract transitional analysis files

| File | Definitions and proofs it owns |
| --- | --- |
| `Abstract/Transition.v` | `AbstractState := point -> A`; pointwise abstraction/concretization and their Galois connection; syntax-directed inductive `local_step` rules; and `Step_sharp a q := unions_sharp D (fun b => exists p, local_step p (a p) q b)`. Define `initial_sharp a0`, `F_sharp a0`, and `Reach_sharp a0 := iteration_limit (F_sharp a0)`. Prove monotonicity, the graph/partition/join characterization, and a conditional fixed-point theorem under abstract omega continuity. |
| `Abstract/TransitionSound.v` | Local simulation by cases on the concrete syntax rule, one-step coverage by the abstract-union soundness field, and global reachability soundness: if `M0` is included in `gamma a0`, then `Reach M P M0` is included in the pointwise concretization of `Reach_sharp P D a0`. Derive the `a0 = alpha M0` corollary. Retain the general invariant lemma that any abstract pre-fixed point covering the initial states covers all concrete reachable states. Prove reachability soundness separately by finite-iterate simulation followed by chain limits, without abstract continuity. |

Prove `local_simulation` directly by cases on the concrete transition derivation, choosing the corresponding abstract syntax rule and using its transfer soundness field. Derive `Step_sound` from the soundness of abstract union of local results.

### 10.5 Examples

`Examples/Assumptions.v` prints the assumptions of the foundational results, successor validity, reachability theorems, abstract soundness results, and key examples; `make audit` replays it and runs `coqchk`.

`Examples/TrivialDomain.v` defines the one-element domain with gamma equal to all memories and its full `AbstractDomain` instance. This is a minimal integration check. Its nonempty concretization of bottom also checks that the generic proofs do not secretly require an empty bottom concretization.

`Examples/NonLatticeDomain.v` defines a CPO with two elements having no common upper bound. Its domain instance has a sound abstract union that returns bottom, proving that the interface requires neither binary joins nor order upper bounds from abstract union. It also instantiates the generic reachability soundness theorem.

`Examples/Examples.v` contains small definitions and proved examples for the semantic checks in Section 7: same-memory assignment, aliasing, independent input choices, initially false/true repeat tests, nonconsecutive labels, nested interior jumps, access to arbitrary integer addresses, missing goto targets, and halt. Instantiate transitional analysis and its soundness theorem with the trivial domain. Use reduction for finite syntax/control-flow and propagation examples; use propositions and proofs for nondeterministic or infinite behavior. No example replaces the generic soundness proof.

### 10.6 Dependency and implementation order

The main dependency paths are:

```text
Sets -> Order -> Fixpoint
Syntax -> ControlFlow
ControlFlow + Fixpoint -> Language.Semantics
Language.Semantics + Order -> Abstract.Domain
ControlFlow + Abstract.Domain + Fixpoint -> Abstract.Transition
Language.Semantics + Abstract.Transition -> Abstract.TransitionSound
Abstract.Domain -> Examples.TrivialDomain
All implementation branches -> Examples.Examples
```

These are logical dependencies, not a requirement to import every transitive dependency directly. Concrete semantics never imports an abstract-domain instance. Abstract propagation builds on the shared syntax, memory, program metadata, transfers, and fixed-point machinery.

Implement and verify in this order:

1. **Foundations and language:** compile the CPO/fixed-point library, syntax, memory, and well-formed program traversal. Check the solution's nested control-flow example.
2. **Concrete semantics:** compile evaluation, transfers, and transitions; establish finite-path reachability and the pointer/input/loop conventions.
3. **Domain interface and transitional analysis:** compile the record, syntax-directed abstract transitions and partition/join aggregation, and local-to-global soundness with `D` universally quantified.
4. **Integration:** compile the trivial domain instance and examples. Document how to supply a later domain instance.

Each milestone must build before proceeding. Finish with a clean build and `Print Assumptions` for successor validity, local simulation, one-step coverage, and global reachability soundness. Any standard logical principles used by the foundations must be explicit and documented; the core results must contain no `Admitted` proofs or project-specific soundness axioms. Record these as completed checks only after running them, following Section 7.

### 10.7 Completed implementation checks (2026-11-23)

All four implementation milestones above are complete. Verification used Rocq 9.0.1, with focused proof inspection through the Coqtail MCP and whole-project builds through the FlowDown-style Makefile.

| Check | Result |
| --- | --- |
| `make clean` followed by `make audit` | All 15 `.v` files rebuilt successfully. |
| `Print Assumptions` in `Examples/Assumptions.v` | All 22 audited results report `Closed under the global context`. No classical or project-specific axioms are needed. |
| `coqchk` on `DAnalyzer.Abstract.TransitionSound` and `DAnalyzer.Examples.Examples` | Independent kernel checking succeeded. |
| Search for `Admitted`, `admit`, `Axiom`, and `Parameter` in `src/*.v` recursively | No occurrences. Domain assumptions are record fields. |
| Semantic examples in `Examples/Examples.v` | Proved memory correlation, aliased stores, independent input choices, pre-test repeat behavior, access to arbitrary integer addresses, invalid goto targets, constant-true loop nontermination at halt, the nested interior-jump trace, and a full domain instantiation. |

The current implementation provides the mathematical abstract reachability analysis and its soundness proof; production domains and convergence engineering remain deferred as in Section 9.

The string/integer-memory revision was rebuilt and audited with the same checks. `AddressMap` now supplies only an injective naming map, while syntax and `Memory` have no type parameters. `integer_dereference` and `integer_store` verify reads and writes at address `-7`; `name_code_injective` verifies the example address map over all strings.

### 10.8 Transitional presentation revision (2026-11-24)

The implementation now follows the syntax-directed transitional presentation throughout. `Program` belongs to `Language/Syntax.v`; `Language/ControlFlow.v` uses recursive syntax lookup with an inherited continuation to compute lexical continuations and the partial `next`, `nextTrue`, and `nextFalse` metadata. Concrete `step` and abstract `local_step` are inductive relations with matching command cases. `Step_sharp` is defined directly as the join of all local transition results at each destination, with the graph/partition/join form proved equivalent, and `local_simulation` is proved by cases on the concrete transition. The compiled action and edge representation has been removed. The memory model, concrete evaluation, transfers, and transitions are merged into `Language/Semantics.v`, with all definitions preceding the lemmas; the exported types and implicit argument declarations match those of the former modules.

| Check | Result |
| --- | --- |
| `make clean` followed by `make audit` | All 12 source files rebuilt; the assumptions replay and independent `coqchk` succeeded. |
| Types and implicit arguments after merging semantics | `Check` and `Print Implicit` output for every declaration from the former memory and concrete modules matches the output for `Language.Semantics`. |
| `Print Assumptions` | All 33 audited results report `Closed under the global context`, including lookup soundness, completeness, absence, and continuation validity. |
| Source scan | No admitted proofs, axioms, global parameters, or compiled action/edge definitions. |
| Revised examples | Static successors, absence of a static goto successor, missing targets, pre-test repeat behavior, loop nontermination at halt, and the nested interior-jump path are proved directly from metadata and transition rules. |

### 10.9 CPO and abstract-union revision (2026-11-24, historical)

The fixed-point construction and audit results in this subsection are superseded by Section 10.10 below. The separation of CPO and abstract union is retained.

This revision replaces the complete-lattice foundation described in the historical checks above. `CPO` now contains only order, bottom, and chain suprema. Concrete powersets use ordinary set union. The separate `AbstractDomain.unions_sharp` operation carries the monotonicity and concrete-union soundness axioms; binary `union_sharp` is derived. `Step_sharp`, `F_sharp`, the partition characterization, and all soundness proofs now use these operations without assuming that abstract union is a least upper bound or even an order upper bound.

The general CPO `lfp` construction closes bottom under the functional and chain limits, and takes the supremum of these approximants. For monotone functionals their comparability uses `Classical_Prop.classic`. Fixed-point existence and leastness require no continuity, finite height, or widening. The separate Kleene theorem retains its explicit omega-continuity hypothesis.

| Check | Result |
| --- | --- |
| Clean build | All 13 source files rebuilt successfully. |
| `make audit` | All 40 assumption checks replayed; 29 results are closed and 11 report only the standard excluded-middle principle `Classical_Prop.classic`. No other axioms are reported. |
| Independent kernel check | `coqchk` passed for generic soundness, existing examples, and the new nonlattice domain. |
| Nonlattice integration | Proved absence of a common upper bound, sound union that is not an order upper bound, and instantiated reachability soundness. |
| Source scan | No admitted proofs, project-specific axioms, global parameters, or remaining complete-lattice interfaces. |

### 10.10 Lecture-style iteration limits (2026-11-24)

The classical approximant construction from Section 10.9 has been removed. `iteration_limit f` is now the supremum of the natural-number iterates of `f` from bottom. The lecture's `lfp` uses this construction, with fixed-point laws under explicit monotonicity and omega-continuity hypotheses. Concrete `F` satisfies both.

`Reach_sharp` uses `iteration_limit (F_sharp a0)` directly. The abstract functional is assumed only monotone, so global soundness does not claim that this limit is a fixed point. `Reach_sharp_fixed` proves that additional conclusion under abstract omega continuity. The generic `iterate_sound` and `iteration_limit_sound` theorems compare finite iterates and then their limits using monotone concretization; abstract continuity and preservation of chain limits by concretization are unnecessary. The separate pre-fixed invariant lemma is retained.

| Check | Result |
| --- | --- |
| `make clean` followed by `make audit` | All 13 source files rebuilt successfully. |
| `Print Assumptions` | All 44 audited results are closed under the global context; no axioms are reported. |
| Independent kernel check | `coqchk` passed for generic soundness, existing examples, and the nonlattice domain. |
| Focused proof check | Coqtail checked the revised soundness file and confirmed that the global theorem is closed and the abstract fixed-point theorem explicitly requires continuity. |
| Source scan | No classical imports, classical approximants, admitted proofs, axioms, or global parameters. |

### 10.11 TeX alignment with lecture-style proofs (2026-11-24)

`doc/project1/project1_solution.tex` now states the same CPO and abstract-union assumptions as the Rocq interface. Exercise 1 defines abstract semantics by the increasing iteration limit, uses abstract-union soundness for one-step coverage, and proves global soundness by finite-iterate simulation followed by monotone concretization at the limit. The local simulation remains the same command-case proof as `local_simulation`.

Exercise 2 was adjusted to the shared assumptions: abstract branches use abstract union, the abstract interpreter is an iteration limit on a CPO, and its soundness proof compares concrete and abstract finite environments before taking limits. Abstract fixed-point identities are stated only under an additional omega-continuity hypothesis.

Verification: `latexmk -pdf -interaction=nonstopmode -halt-on-error project1_solution.tex` succeeded. The six-page PDF has no LaTeX warnings or overfull/underfull boxes. The rendered Exercise 1 definitions and safety proof were visually checked, and the proof steps were compared with `Abstract/TransitionSound.v` and `Foundations/Fixpoint.v`.
