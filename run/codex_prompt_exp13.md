# Complete Experiment 13 (Intermediate Hardness)

## Context

You are working on a master's thesis on Unstructured Adiabatic Quantum Optimization. The thesis extends the paper "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736). Read `CLAUDE.md` for project guidelines, style, and structure.

Experiment 13 lives in `src/experiments/13_intermediate_hardness/`. Read every file in this directory before doing anything: `main.md`, `proof.md`, `lib/verify.py`, and `lib/deep_verify.py`. Also read `src/experiments/README.md` and `src/experiments/CLAUDE.md` for experiment conventions.

The central question: **What is the complexity of estimating A_1 to precision 2^{-n/2}?** This is the precision the adiabatic algorithm needs, and it falls between the paper's two hardness regimes (NP-hard at 1/poly(n), #P-hard at 2^{-poly(n)}). The answer (already established): quantum Theta(2^{n/2}), classical Theta(2^n); quadratic quantum-classical separation.

**Critical context: neighboring experiments.** Before doing any work, read the `main.md` files of:
- `src/experiments/08_structured_tractability_v2/main.md` -- structured families where A_1 may be tractable even at 2^{-n/2}
- `src/experiments/10_information_theoretic/main.md` -- bit-runtime tradeoff (each bit of A_1 halves adiabatic runtime)
- `src/experiments/12_circumventing_barrier/main.md` -- Hamiltonian modifications cannot avoid needing A_1


## What Is Already Done (DO NOT REDO)

Status: RESOLVED. 7 theorems proved. Tight bounds in both query and computational models. No Lean formalization.

**Completed results:**
- Theorem 1 (Interpolation Barrier): polynomial interpolation technique fails at epsilon = 2^{-n/2}; amplified error exceeds 1/2
- Theorem 2 (Quantum Algorithm): O(2^{n/2} * poly(n)) via amplitude estimation
- Theorem 3 (Classical Lower Bound): Omega(2^n) via Le Cam / KL divergence
- Theorem 4 (Tight Quantum Bound): Omega(1/epsilon) quantum lower bound via Heisenberg limit + approximate counting equivalence; combined with Theorem 2: Theta(2^{n/2})
- Theorem 5 (ETH Computational Bound): under ETH, classical requires 2^{Omega(n)} time
- Theorem 6 (Generic Extrapolation Barrier): ANY polynomial extrapolation scheme of degree d amplifies errors by at least 2^{d-1}; not specific to paper's construction
- Theorem 7 (Structure Irrelevance): M=2 instances are worst-case; sum-of-reciprocals structure provides no advantage
- Corollary: quadratic quantum-classical separation at epsilon = 2^{-n/2}

Tight landscape: quantum Theta(1/epsilon), classical Theta(1/epsilon^2).


## What Is Missing (THE ACTUAL WORK)

### Gap 1: Precision Landscape (Complexity Transitions Across Precisions)

The experiment resolves complexity at epsilon = 2^{-n/2} but doesn't map the full precision landscape. The paper gives three points: NP-hard at 1/poly(n), an open regime at 2^{-n/2}, and #P-hard at 2^{-poly(n)}. This experiment resolves the middle point. But the transitions between regimes are uncharacterized.

**Concrete target:**

Write a "Precision Phase Diagram" proposition or structured remark that maps complexity as a function of precision epsilon:

1. **epsilon = Theta(1)**: trivially approximable (A_1 is bounded; output 0).
2. **epsilon = 1/poly(n)**: NP-hard (paper Theorem 2). Quantum: O(poly(n)) queries if Delta_1 = Theta(1) (Theorem 2 with epsilon = 1/poly). Classical: Omega(poly(n)) queries (Theorem 3).
3. **epsilon = 2^{-cn} for c < 1/2**: intermediate. Quantum: O(2^{cn} poly(n)). Classical: Omega(2^{2cn}). Separation factor: 2^{cn}. The gap grows continuously with c.
4. **epsilon = 2^{-n/2}**: the algorithmically relevant threshold. Quantum: Theta(2^{n/2}). Classical: Theta(2^n). This is where polynomial interpolation breaks.
5. **epsilon = 2^{-cn} for c > 1/2**: #P-hard (paper Theorem 3 applies for sufficiently large c). Quantum: O(2^{cn} poly(n)). Classical: at least #P-hard.
6. **epsilon = 2^{-poly(n)}**: #P-hard (paper Theorem 3). Exact degeneracy extraction possible.

The key insight: complexity transitions smoothly with precision; epsilon = 2^{-n/2} is the structural boundary where interpolation-based techniques break, but there is no sharp "phase transition" in query complexity -- it grows continuously as Theta(1/epsilon) quantum, Theta(1/epsilon^2) classical.

Write this as a Proposition with proof (chain existing results). Add a figure-like table to proof.md.

### Gap 2: Structured Instance Investigation (Connection to Exp 08)

Theorem 7 proves M=2 instances are worst-case for unstructured problems. But Exp 08 identifies structured families (bounded treewidth, ferromagnetic Ising) where A_1 is classically tractable.

**Concrete target:**

Proposition: For the structured families identified in Exp 08 (bounded treewidth, ferromagnetic Ising with consistent fields):
1. Does Theorem 7's worst-case argument apply? (Likely not -- the "concentrate degeneracy in first two levels" construction may violate structural constraints.)
2. If not: what is the complexity of A_1 estimation at precision 2^{-n/2} for these families? Can they be solved in poly time classically (making AQO practical)?
3. State the precise conditions under which Exp 08's tractability results extend to the schedule-relevant precision 2^{-n/2}.

This connects Exp 13 (hardness) to Exp 08 (tractability) in a way neither experiment currently does. Import results from Exp 08 by citation.

### Gap 3: Promise Class Characterization (Open Question #1)

The experiment's open question #1 asks: is A_1 estimation at 2^{-n/2} complete for some natural promise complexity class?

**Concrete target (attempt, may not resolve):**

(a) A_1 estimation is a promise/function problem. The promise is that Delta_1 >= 1/poly(n) (nontrivial gap). The function outputs a real number to precision epsilon. Identify the closest natural complexity class.

(b) Candidate: PromiseBQP (quantum polynomial time with promise). The quantum algorithm (Theorem 2) runs in time O(2^{n/2} poly(n)), which is NOT polynomial. So A_1 estimation is NOT in PromiseBQP at epsilon = 2^{-n/2}.

(c) More precisely: A_1 estimation at precision epsilon is in BQTIME(1/epsilon * poly(n)). At epsilon = 2^{-n/2}, this gives BQTIME(2^{n/2} poly(n)). Is there a matching lower bound conditional on standard assumptions?

(d) If a clean characterization emerges, state it as a proposition. If the analysis is inconclusive, write a Remark documenting what was tried and why standard promise classes don't cleanly capture this problem.

### Gap 4: Chapter 9 Integration Plan

**Concrete tasks:**

1. Read the Chapter 9 outline in `README.md`. Exp 13's results complement Exp 08 (structured tractability) and Exp 10 (model separation). The natural placement is in the section connecting hardness results to information costs -- perhaps as a subsection of the "Central Claim" section, or as a bridge between the Ignorance Taxonomy and the model separation capstone.

2. Write a Chapter 9 insertion outline. The experiment's main contribution to the thesis narrative: "The paper proves A_1 is NP-hard at 1/poly and #P-hard at exponential precision. We prove that at the algorithmically relevant precision 2^{-n/2}, there is a clean quadratic quantum-classical separation. This quantifies the information cost of the adiabatic model."

3. Add to `todo.md`.


## Deliverables and Quality Standards

### What to produce:

1. **New results in `proof.md`**: precision landscape (Gap 1) as a new section after the Updated Complexity Landscape. Structured instance proposition (Gap 2) as a section connecting to Exp 08. Promise class remark (Gap 3) if progress is made.

2. **Updated `lib/verify.py`**: add verification for the precision landscape (compute quantum/classical bounds at multiple epsilon values and verify they match the claimed scaling).

3. **New `todo.md`**: create with Plans, Progress, Findings sections.

4. **Updated `main.md`**: add cross-experiment connections to Exps 08, 10, 12. Update Open Questions.

### Quality standards (from CLAUDE.md):

- Every sentence must carry information. No filler.
- State results with explicit bounds and dependencies.
- All math must follow correct LaTeX conventions.
- No non-ASCII characters.

### Correctness requirements:

- The precision landscape must correctly classify each regime. Cite the exact theorem that applies at each precision level.
- Structured instance claims must verify that Theorem 7's construction respects (or violates) structural constraints.
- Promise class discussion must be honest about what is and isn't established.


## Execution Strategy

1. Read all files in the experiment directory.
2. Read main.md of Exps 08, 10, 12.
3. Read `CLAUDE.md`.
4. Create `todo.md`.
5. Start with Gap 1 (precision landscape) -- cleanest contribution, chains existing results.
6. Then Gap 2 (structured instances) -- connects to Exp 08, moderate difficulty.
7. Then Gap 4 (Chapter 9 outline).
8. Gap 3 (promise class) only if time permits -- speculative.
9. Re-read proof.md for consistency.


## Success Criteria

The experiment is COMPLETE if:
- The precision landscape (Gap 1) is stated and proved
- The structured instance analysis (Gap 2) produces a proposition or remark
- todo.md and Chapter 9 outline exist
- All numerics pass

The experiment achieves NOVELTY if:
- The precision landscape provides the definitive "complexity vs precision" map for A_1 estimation
- The structured instance analysis reveals that Exp 08's tractability extends (or fails to extend) to 2^{-n/2}
- The results integrate into Chapter 9 as the quantitative bridge between hardness and information cost


## What NOT to do

- Do NOT re-derive Theorems 1--7. They are correct and verified.
- Do NOT re-derive results from other experiments. Import by citation.
- Do NOT modify files outside `src/experiments/13_intermediate_hardness/`.
- Do NOT attempt Lean formalization (lower priority than content gaps).
- Do NOT write vague discussions. Every claim must be precise.
- Do NOT introduce new notation without checking proof.md's existing conventions.
