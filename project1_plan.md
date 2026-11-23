# Project 1 plan: generic abstract interpretation for D

Prepared: 2026-11-20  
Deadline stated in project1.pdf: November 25, in class.

Rocq implementation structure added: 2026-11-23.

## 1. Objective and scope

Formalize the transitional analysis in [project1_solution.tex](project1_solution.tex) as a generic program analyzer in Rocq, covering Exercise 1 in [project1.pdf](project1.pdf): concrete collecting semantics, a generic abstract transition system, and local-to-global reachability soundness.

The current assignment explicitly allows all abstract domains to remain parameters connected to concrete powersets by Galois connections. Package the abstract memory domain, its auxiliary operations, and their proof obligations in an `AbstractDomain` record, and parameterize the analyzer and its proofs by a value of that record. Section 10 specifies the Rocq files and their interfaces. A parser, production congruence or relational domains, and the final watercheck tool remain deferred.

Use [project.pdf](project.pdf) for the complete syntax and the eventual watermark objective. Treat the requirements in project1.pdf as authoritative for this submission.

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
- **Values and memory:** a simple candidate is V = Z, a finite set of variables Var(P), an injective address map addr : Var(P) → Z, and M = Var(P) → Z. Then &x denotes addr(x), while *x accesses the variable whose address equals m(x). This preserves integer-valued addresses and numeric jump targets without inventing disjoint pointer types. State initialization assumptions through M0 rather than silently setting variables to zero.
- **Input:** readInt nondeterministically returns any integer on every evaluation. There is no input stream in the required state L × M. Treat repeated occurrences as independent choices.
- **Truth:** use zero for false, nonzero for true; E1 < E2 produces 0 or 1.
- **Invalid operations:** explicitly select a policy for invalid addresses and nonexistent jump labels. A defensible baseline is stuck execution, with no successor. This is a modeling choice, not an explicit requirement in the PDFs. An error-state alternative requires extending the state space consistently.
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
| Memory union | union : P(M) × P(M) → P(M) | join : M# × M# → M# |
| Identity | id : P(M) → P(M) | id# : M# → M# |

The expression-evaluation row is an optional extension. Following the solution, the initial Rocq implementation uses whole-memory assignment, store, guard, and target operations and therefore does not require a separate abstract value domain.

For example:

- assign_x,E(X) = {m[x ↦ v] | m ∈ X, v ∈ Eval_E(m)}.
- store_x,E(X) = {m[y ↦ v] | m ∈ X, addr(y) = m(x), v ∈ Eval_E(m)}.
- assume_E,true(X) = {m ∈ X | some v ∈ Eval_E(m) is nonzero}; false selects a possible zero.
- target_E,k(X) = {m ∈ X | k ∈ Eval_E(m)}.

Define Eval for every expression constructor: n, addition, multiplication, negation, comparison, x, *x, &x, and readInt. Arithmetic combines possible operand values within the same memory. Invalid dereferences produce no result under the provisional stuck policy.

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

Use A = L → M#, pointwise ordering/join, and:

- α_S(X)(l) = α_M({m | (l,m) ∈ X}).
- γ_S(a) = {(l,m) | m ∈ γ_M(a(l))}.

There is a type discrepancy to resolve explicitly: project1.pdf p. 2 describes the abstract one-step relation over label maps, whereas slide8.pdf pp. 17 and 34 use local pairs (L × M#). The printed partition-and-join formula naturally uses the latter.

Present both layers:

1. A local abstract edge relation over (L × M#), using each abstract transfer.
2. Its aggregate Step# : A → A, joining all incoming contributions at each destination.

If retaining the handout's map-to-map relation notation, define its meaning in terms of these contributions; do not apply partitioning to a map-to-map relation without a typed bridge.

For goto, enumerate the finite set of original labels k and propagate target_E,k#(a(l)) to k. This avoids assuming that V# itself supports target enumeration. Unknown targets may conservatively propagate to all original labels.

Set I# = α_S(I), F#(a) = I# join Step#(a), and Reach# = lfp F#. Empty collections of contributions join to bottom. Do not assume γ_M(bottom) is empty unless justified by the chosen connection.

### 5.4 Prove soundness

Prove local edge coverage case by case: every concrete edge from a represented source memory is covered by the corresponding abstract contribution. The key cases are indirect store, nondeterministic guards, and computed goto.

Then show:

1. Step(γ_S(a)) ⊆ γ_S(Step#(a)).
2. F(γ_S(a)) ⊆ γ_S(F#(a)).
3. lfp F ⊆ γ_S(lfp F#).

For the final step, use fixed-point transfer or show that γ_S(lfp F#) is a concrete pre-fixed point. Type-check the relation-level formula in the handout through the local-pair lifting before invoking it.

## 6. Deferred scope

Exercise 2, the definitional interpreter, is deferred. Its mathematical design remains in `project1_solution.tex`; it has no files or milestones in the current Rocq implementation plan.

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
| Check invalid pointer/target and terminal behavior | Undocumented or inconsistent boundary semantics |
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

The solution draft is now in `project1_solution.tex`. The Rocq implementation should follow the dependency order and completion checks in Section 10. Formatting/submission details beyond the stated deadline are not specified in the supplied PDFs.

## 9. Deferred watercheck implementation

After this assignment, instantiate the generic memory domain to support:

- P1: integer values congruent to 123 modulo 260401.
- P2: a relation between variables whose sum is always 123.
- Pointer aliasing, indirect stores, and computed jump targets.
- Convergence engineering, worklist scheduling, and possibly widening.

Watermark claims concern all reachable memories at a chosen program point. Distinguish command entry from command exit, especially when unrelated goto edges also reach the successor. Avoid claiming a watermark merely because a point is unreachable, or inferring that failure to prove a watermark establishes its absence.

## 10. Rocq project structure

This section is the implementation design; the listed `.v` files have not yet been created. Use the logical namespace `DAnalyzer`, with `-Q theories DAnalyzer` in `_CoqProject`. Keep definitions and their supporting lemmas together; place the main reachability soundness proof in a dedicated file.

### 10.1 Planned layout

```text
_CoqProject
Makefile
README.md
theories/
  Foundations/
    Sets.v
    Order.v
    Fixpoint.v
  Language/
    Syntax.v
    Memory.v
    Program.v
  Concrete/
    Expression.v
    Transfer.v
    Transition.v
  Abstract/
    Domain.v
    Transition.v
    TransitionSound.v
  Examples/
    TrivialDomain.v
    Examples.v
```

`_CoqProject` lists the namespace mapping and source files. `Makefile` wraps the installed Rocq build generator and exposes `make`, `make clean`, and an assumptions audit target. Generated build files and compiled artifacts are ignored by Git. `README.md` records the verified toolchain, build commands, main theorem names, and current scope. Confirm the installed Rocq version before selecting import paths or generator commands.

### 10.2 Foundations and language files

| File | Definitions and proofs it owns |
| --- | --- |
| `Foundations/Sets.v` | `set A := A -> Prop`, subset, empty set, union, indexed union, relational image, and elementary inclusion lemmas. Sets are predicates, not finite lists. |
| `Foundations/Order.v` | A bundled `CompleteLattice` record; order laws, monotonicity, bottom, binary join, arbitrary supremum, derived infimum, and pointwise lattices for predicates and maps. Use mutual ordering as equivalence, so function equality is not needed to state lattice laws. |
| `Foundations/Fixpoint.v` | `lfp` as the infimum of pre-fixed points, its fixed-point and leastness laws for monotone functionals, natural-number iteration, and the Kleene characterization under an explicit increasing-chain continuity hypothesis. This file contains no D-specific definitions. |
| `Language/Syntax.v` | Expressions with all nine constructors and labeled commands with all six constructors; `label`, command-occurrence traversal, and expression/command variable traversal. Syntax is parameterized by a variable type; source labels are `nat`, integer constants are `Z`, and `halt` is not a syntax constructor. |
| `Language/Memory.v` | A `MemoryModel` record containing a finite variable type, its complete enumeration and decidable equality, and an injective integer address map. Define `Memory := Var -> Z`, functional update, address lookup, and lookup/update lemmas. Initial memory sets remain inputs. |
| `Language/Program.v` | A well-formed `Program` record over the syntax, requiring distinct labels; finite `Entry P` indices corresponding to actual command occurrences; label/command lookup and their correspondence; `Point P := Halt | At (Entry P)`; and finite point enumeration. Implement `build C k`, lexical continuations, and a finite list of control-flow edges. Prove the traversal's constructor equations, valid endpoints, and coverage. Resolve integer goto targets only through lookup among source entries. |

`Entry P` identifies an occurrence in the fixed whole program and retains its lexical continuation when a jump enters a nested command. Representing `Halt` separately also prevents it from becoming an integer jump target.

Define edge actions in `Language/Program.v` as a small datatype: identity, direct assignment, indirect store, true/false guard, and target filter. A goto contributes one candidate edge per source entry, tagged with that entry's integer label. An if or repeat contributes both guard edges. Preserve separate edge contributions even if their endpoints coincide; give goto no fall-through edge and halt no outgoing edges.

### 10.3 Concrete semantics and the abstract-domain interface

| File | Definitions and proofs it owns |
| --- | --- |
| `Concrete/Expression.v` | `eval : expr Var -> Memory -> Z -> Prop`, equivalently memory-indexed value sets; rules for arithmetic, comparison, variables, addresses, dereference, and independent nondeterministic `readInt`; the powerset extension `eval_set`. Prove the basic constructor equations and invalid-address behavior. |
| `Concrete/Transfer.v` | Exact `assign`, `store`, `assume`, and `target` operations on memory sets; identity; and `transfer` interpreting an edge action. Prove monotonicity and preservation of arbitrary unions, including the empty union. All expression choices and pointer resolution use the same pre-update memory. |
| `Concrete/Transition.v` | State type `Point P * Memory`; constructor-based `step`; edge-based characterization using `transfer`; finite-path closure; initial states, collecting `Step`, `F`, and `Reach`. Prove monotonicity, continuity, the fixed-point characterization, and equivalence of `Reach` with finite execution prefixes. |
| `Abstract/Domain.v` | The `AbstractDomain` record described below, plus derived concretization monotonicity, coverage of bottom/join contributions, and a generic soundness lemma for interpreting any edge action. This file depends on concrete transfers, never on abstract propagation or its soundness proof. |

Use one explicit record argument `D : AbstractDomain M` for a fixed `M : MemoryModel`. Its bundled lattice supplies the abstract carrier `A`. The intended fields are:

| Field or field group | Type/obligation |
| --- | --- |
| `memory_lattice` | A `CompleteLattice`, exposing carrier `A`, order `le`, computational `bottom` and `join`, and mathematical arbitrary suprema. Bottom and join have their bound/least-upper-bound laws and agree with the corresponding suprema up to order equivalence. |
| `alpha`, `gamma` | `alpha : set Memory -> A` and `gamma : A -> set Memory`. |
| `galois` | For every `X` and `a`, `le (alpha X) a <-> subset X (gamma a)`. |
| `assign_sharp` | `Var -> expr Var -> A -> A`. |
| `store_sharp` | `Var -> expr Var -> A -> A`. |
| `assume_sharp` | `expr Var -> bool -> A -> A`, with `true` selecting nonzero results. |
| `target_sharp` | `expr Var -> nat -> A -> A`, testing the integer denoted by a source label. |
| Transfer monotonicity | One proof for each operation, pointwise in its syntax parameters. |
| Transfer soundness | One proof for each operation: `T (gamma a)` is included in `gamma (T_sharp a)`. |

Store these data and proofs in the record rather than declaring unrelated global `Parameter`s or assuming global soundness axioms. Analyzer sections take `P` and `D` explicitly; adding a domain instance should require no changes to analyzer definitions or proofs. Other auxiliaries, such as abstract edge transfer and finite joins, are derived uniformly from `D`. Abstract identity is the actual identity function.

No field assumes that `gamma bottom` is empty, that gamma preserves joins, or that abstract memories have a variable-wise product representation. A separate abstract value domain is unnecessary for these whole-memory transfers; add a separate optional interface if expression analysis later needs one. Keep arbitrary suprema and `alpha` in the semantic interface. Define abstract reachability from a supplied abstract input `a0` and derive the `a0 = alpha M0` corollary.

### 10.4 Abstract transitional analysis files

| File | Definitions and proofs it owns |
| --- | --- |
| `Abstract/Transition.v` | `AbstractState := Point P -> A`; pointwise abstraction/concretization and their Galois connection; abstract edge transfers; the local pair relation; and `Step_sharp` as a finite fold joining every incoming edge contribution. Define `initial_sharp a0`, `F_sharp a0`, and `Reach_sharp a0 := lfp (F_sharp a0)`. Prove monotonicity and the graph/partition/join characterization from the solution. |
| `Abstract/TransitionSound.v` | Local edge coverage, one-step simulation, and global reachability soundness: if `M0` is included in `gamma a0`, then `Reach P M0` is included in the pointwise concretization of `Reach_sharp P D a0`. Derive the `a0 = alpha M0` corollary. Prove the general invariant lemma that any abstract pre-fixed point covering the initial states covers all concrete reachable states, then specialize it to the least fixed point. |

Connect abstract edge propagation to the constructor-based concrete step rules through the edge characterization in `Concrete/Transition.v`. This checks both the control-flow traversal and the abstract transfer interface.

### 10.5 Examples

`Examples/TrivialDomain.v` defines the one-element domain with gamma equal to all memories and its full `AbstractDomain` instance. This is a minimal integration check. Its nonempty concretization of bottom also checks that the generic proofs do not secretly require an empty bottom concretization.

`Examples/Examples.v` contains small definitions and proved examples for the semantic checks in Section 7: same-memory assignment, aliasing, independent input choices, initially false/true repeat tests, nonconsecutive labels, nested interior jumps, invalid addresses/targets, and halt. Instantiate transitional analysis and its soundness theorem with the trivial domain. Use reduction for finite syntax/control-flow and propagation examples; use propositions and proofs for nondeterministic or infinite behavior. No example replaces the generic soundness proof.

### 10.6 Dependency and implementation order

The main dependency paths are:

```text
Sets -> Order -> Fixpoint
Syntax -> Memory -> Expression -> Transfer
Syntax -> Program
Program + Transfer + Fixpoint -> Concrete.Transition
Transfer + Order -> Abstract.Domain
Program + Abstract.Domain + Fixpoint -> Abstract.Transition
Concrete.Transition + Abstract.Transition -> Abstract.TransitionSound
Abstract.Domain -> Examples.TrivialDomain
All implementation branches -> Examples.Examples
```

These are logical dependencies, not a requirement to import every transitive dependency directly. Concrete semantics never imports an abstract-domain instance. Abstract propagation builds on the shared syntax, memory, program metadata, transfers, and fixed-point machinery.

Implement and verify in this order:

1. **Foundations and language:** compile the lattice/fixed-point library, syntax, memory, and well-formed program traversal. Check the solution's nested control-flow example.
2. **Concrete semantics:** compile evaluation, transfers, and transitions; establish finite-path reachability and the pointer/input/loop conventions.
3. **Domain interface and transitional analysis:** compile the record, finite abstract propagation, and local-to-global soundness with `D` universally quantified.
4. **Integration:** compile the trivial domain instance and examples. Document how to supply a later domain instance.

Each milestone must build before proceeding. Finish with a clean build and `Print Assumptions` for local edge coverage, one-step simulation, and global reachability soundness. Any standard logical principles used by the foundations must be explicit and documented; the core results must contain no `Admitted` proofs or project-specific soundness axioms. Record these as completed checks only after running them, following Section 7.
