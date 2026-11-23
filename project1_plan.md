# Project 1 plan: generic abstract interpretation for D

Prepared: 2026-11-20  
Deadline stated in project1.pdf: November 25, in class.

## 1. Objective and scope

Produce a mathematical design and soundness argument for both exercises in [project1.pdf](project1.pdf):

1. Transitional collecting semantics, a generic abstract transition system, and local-to-global soundness.
2. A collecting definitional interpreter, a homomorphic abstract interpreter, and fixed-point soundness.

The current assignment explicitly allows all abstract domains to remain parameters connected to concrete powersets by Galois connections. Do not spend this stage implementing a parser, choosing congruence or relational domains, or building the final watercheck tool.

Use [project.pdf](project.pdf) for the complete syntax and the eventual watermark objective. Treat the requirements in project1.pdf as authoritative for this submission.

## 2. Reading map

Page references below mean PDF pages, not printed lecture slide numbers.

| Source | Relevant material | Planned use |
| --- | --- | --- |
| project1.pdf, pp. 1–3 | Exercise 1 and its proof obligation | Submission checklist for transitional semantics |
| project1.pdf, pp. 3–5 | Exercise 2 and its proof obligation | Interpreter equations, operator types, correctness |
| project.pdf, p. 2 | D syntax, addresses, readInt, computed goto | Complete constructor inventory |
| project.pdf, pp. 2–3 | P1/P2 and watermark example; AI verification requirement | Future compatibility and verification record |
| lecture slide/slide8.pdf, pp. 5–9, 17–22, 33–35 | Reachability fixed point, label maps, partitioning and joining | Exercise 1 framework |
| lecture slide/slide8.pdf, pp. 38–44 | Concrete/abstract transition example and operator soundness | Rule and proof templates, extended for D |
| lecture slide/slide3-0.pdf, pp. 1–8 | Transitional collecting semantics | Short cross-check of reachability definitions |
| lecture slide/slide7.pdf, pp. 13–17 | Collecting/abstract interpreters and correctness | Exercise 2 template, adapted for nonlocal goto |
| lecture slide/slide5.pdf, p. 6 | Fixpoint transfer theorem | Soundness proof architecture |
| lecture slide/slide2.pdf | Semantic domains, continuity, recursive equations | Existence of interpreter fixed points |

Use the slides as templates, not as equations to copy without checking. For example, slide7.pdf p. 16 prints the first branch interpreter twice in the conditional equation; the false branch must use the second branch.

## 3. Settle the semantic conventions first

Write a short conventions section before either exercise. Distinguish source requirements from assumptions where the sources leave behavior unspecified.

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

For example:

- assign_x,E(X) = {m[x ↦ v] | m ∈ X, v ∈ Eval_E(m)}.
- store_x,E(X) = {m[y ↦ v] | m ∈ X, addr(y) = m(x), v ∈ Eval_E(m)}.
- assume_E,true(X) = {m ∈ X | some v ∈ Eval_E(m) is nonzero}; false selects a possible zero.
- target_E,k(X) = {m ∈ X | k ∈ Eval_E(m)}.

Define Eval for every expression constructor: n, addition, multiplication, negation, comparison, x, *x, &x, and readInt. Arithmetic combines possible operand values within the same memory. Invalid dereferences produce no result under the provisional stuck policy.

Using whole-command transfer operators as primitives keeps the abstract memory domain fully generic and permits relational domains later. If the final exposition decomposes them into lookup, dereference, arithmetic, and update operators, add the corresponding types and proof obligations; do not leave those interfaces implicit.

**Exactness checkpoint:** independently computing eval_E(X) and crossing it with every memory in X can introduce values from unrelated memories. That may be a sound abstraction, but is not the exact natural powerset collecting semantics requested for Exercise 2.

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

## 6. Exercise 2 work packages

### 6.1 Define what the interpreter returns

The required interface is I : Cmd → P(M) → P(M), and its natural interpretation is final memories of terminating executions. Unlike Exercise 1, it does not automatically record every intermediate state.

A naive compositional equation I(C1;C2) = I(C2) ∘ I(C1), together with goto calling only its target subtree, mishandles nonlocal jumps. Resolve this using the fixed whole-program context P.

Use each uniquely labeled Cmd as an entry into its **residual execution to halt** in P. This retains the required command-indexed interface; the meaning of an interior command depends on its context in P. State this explicitly. Interpret the top-level C as the whole program. No synthetic loop entries are needed.

### 6.2 Write mutually recursive collecting equations

Use an auxiliary environment H : L → (P(M) → P(M)), including halt. Planned equations include:

- H(halt)(X) = X.
- Direct assignment at l: H(l)(X) = H(next(l))(assign_x,E(X)).
- Indirect assignment: use store_x,E analogously.
- Sequence entry: H(l)(X) = H(firstChild(l))(X).
- If: union the true and false successor calls after their guard filters.
- Repeat at l with body B and exit k: H(l)(X) = H(label(B))(assume_E,true(X)) ∪ H(k)(assume_E,false(X)). The body's normal continuation is l.
- Goto: H(l)(X) = union over valid original labels k of H(k)(target_E,k(X)).

Define the functional Φ whose least fixed point solves these equations. Set I_P(C) = (lfp Φ)(label(C)). Explain how the finite auxiliary equations are substituted or encoded to obtain the assignment's command-indexed functional F and its abstract counterpart; do not present the auxiliary environment as an unexplained change of interface.

The bottom environment returns the empty set everywhere. Establish continuity in the environment argument and that finite unfoldings describe finite terminating executions. Infinite executions contribute no final memories.

### 6.3 Define the abstract interpreter homomorphically

Replace each transfer by its # version, unions by joins, identity by identity, and recursive calls by calls in the abstract environment. Preserve the equation structure.

Define the abstract environment type, its pointwise order, Φ#, and I_P#. After accounting for the auxiliary entries, state the requested command-indexed F# and C# = (lfp F#)(C).

Keep domains generic. The existence of the abstract least fixed point and any use of Kleene iteration require explicit domain/continuity assumptions; finite-time computability is a separate later concern.

### 6.4 Prove interpreter soundness

Use a relation between concrete and abstract interpreter environments:

H is represented by H# when, for every entry l and abstract input a,
H(l)(γ_M(a)) ⊆ γ_M(H#(l)(a)).

Show bottom environments are related, and show Φ and Φ# preserve this relation. Composition cases also use monotonicity of concrete environment functions. Handle limits with the stated continuity/order assumptions, or use a suitable fixed-point simulation theorem.

Conclude, for every whole program C and abstract input a:

C(γ_M(a)) ⊆ γ_M(C#(a)).

For a concrete input set M0, choose a0 = α_M(M0) and derive
C(M0) ⊆ γ_M(C#(a0)).

As a consistency check, final memories from Exercise 2 must equal memories at halt reachable in Exercise 1 under the same conventions.

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
| Compare finite interpreter unfoldings with finite paths to halt | Interpreter/transition mismatch |
| Check a reachable infinite loop | Confusing reachability with terminating outputs |
| Type-check every operator and lifting formula | Mixing memory sets, value sets, local pairs, and label maps |
| Check every local proof and its fixed-point assumptions | Treating experiments or local soundness as a global proof |

Small bounded traces can detect errors but cannot establish soundness for all D programs. The submission needs the case analysis and fixed-point arguments.

## 8. Work sequence before November 25

| Target | Work | Exit condition |
| --- | --- | --- |
| Nov. 20 | Requirements, conventions, domain/operator tables | Every ambiguity and assumption is visible |
| Nov. 21 | Static successors and concrete transitional semantics | All constructors covered; nested jump and repeat traces checked |
| Nov. 22 | Abstract transitions and Exercise 1 proof | Typed Step# and complete local-to-global argument |
| Nov. 23 | Concrete/abstract interpreter equations | Nonlocal goto handled; required interface explained |
| Nov. 24 | Exercise 2 proof and cross-checks | Soundness and agreement at halt; AI verification record completed |
| Before Nov. 25 class | Final notation and requirement audit | Both exercises complete and consistent |

The next written artifact should be the solution draft with this order: shared conventions; Exercise 1 control/rules/proof; Exercise 2 equations/proof; verification record. Formatting/submission details beyond the stated deadline are not specified in the supplied PDFs.

## 9. Deferred watercheck implementation

After this assignment, instantiate the generic memory domain to support:

- P1: integer values congruent to 123 modulo 260401.
- P2: a relation between variables whose sum is always 123.
- Pointer aliasing, indirect stores, and computed jump targets.
- Convergence engineering, worklist scheduling, and possibly widening.

Watermark claims concern all reachable memories at a chosen program point. A final-memory interpreter alone is insufficient for those intermediate-point queries without instrumentation. Distinguish command entry from command exit, especially when unrelated goto edges also reach the successor. Avoid claiming a watermark merely because a point is unreachable, or inferring that failure to prove a watermark establishes its absence.
