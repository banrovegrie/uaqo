# Complete Experiment 10 (Information-Theoretic Limits)

## Context

You are working on a master's thesis on Unstructured Adiabatic Quantum Optimization. The thesis extends the paper "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736). Read `CLAUDE.md` for project guidelines, style, and structure.

Experiment 10 lives in `src/experiments/10_information_theoretic/`. Read every file in this directory before doing anything: `main.md`, `proof.md`, the Lean files in `lean/`, and `lib/verify.py`. Also read `src/experiments/README.md` and `src/experiments/CLAUDE.md` for experiment conventions.

The central question of this experiment: **Is the A_1 barrier a fundamental information-theoretic limit, or an artifact of the adiabatic model?** The answer (already established): model-specific artifact. Circuit algorithms (Durr-Hoyer) bypass it entirely.

**Critical context: neighboring experiments.** Before doing any work, also read the `main.md` files of experiments 12, 13, and 08 (at minimum). These are:
- `src/experiments/12_circumventing_barrier/main.md` — proves the A_1 barrier is unbreakable within rank-one instance-independent design (No-Go theorem)
- `src/experiments/13_intermediate_hardness/main.md` — resolves complexity of estimating A_1 at precision 2^{-n/2}: quantum O(2^{n/2}), classical Omega(2^n)
- `src/experiments/08_structured_tractability_v2/main.md` — characterizes when A_1 is tractable via partition-function complexity

These experiments provide results that experiment 10 should import, synthesize, and build on. The prompt below specifies exactly how.


## What Is Already Done (DO NOT REDO)

The experiment is in "EXTENDED" phase with substantial completed work. 7+ theorems in `proof.md`, 14 Lean-verified theorems, 5 passing numerical test suites.

**Resolved results:**
- Theorem 1: Universal query lower bound Omega(sqrt(N/d_0)) (BBBV)
- Theorem 2: Durr-Hoyer achieves O(sqrt(N/d_0)) without any spectral information
- Theorem 3: Model separation (circuit = 0 bits; adiabatic fixed = Theta(n) bits; adaptive = 0 bits)
- Theorem 4: Communication complexity formalization (Alice-Bob model)
- Theorem 5: Refutation of "No Free Lunch" conjecture via Durr-Hoyer
- Propositions 6-8: A_1-blindness of circuit algorithms (I(X_DH; A_1 | S_0, E_0) <= 2^{-Omega(n)})
- Theorem 6: Interpolation import from Exp 07 (T(epsilon) = T_inf * Theta(max(1, epsilon/delta_{A_1})))
- Theorem 7: Bit-runtime tradeoff (T(C) = T_inf * 2^{n/2-C}; each bit halves runtime)
- Conjecture 5: Continuous-time A_1 barrier — STATED with evidence FOR and AGAINST but **OPEN**

**Resolved conjectures:** 1 (proved), 2 (refined), 3 (proved with corrected framing), 4 (refuted). Conjecture 5 remains open.

This is solid work. The experiment's boundary-setting and core model-separation results are complete.


## What Is Missing (THE ACTUAL WORK)

There are four gaps. Gaps 1 and 2 are the highest-value targets for novelty. Gaps 3 and 4 provide synthesis and narrative closure.

### Gap 1: Cross-Experiment Synthesis Theorem

The experiment currently operates in isolation. Experiments 12, 13, and 08 have produced results that, when combined with Exp 10's framework, yield a stronger unified statement than any experiment alone. This synthesis is the single highest-value contribution remaining.

**Concrete target: a "Complete Model Comparison Theorem" that integrates results from Exp 10, 12, 13, and 08.**

The theorem should state something like: for unstructured ground-state finding on n-qubit diagonal Hamiltonians with d_0 marked states:

| Model | Spectral Info Required | Runtime | Info Source | Barrier |
|-------|----------------------|---------|-------------|---------|
| Circuit (Durr-Hoyer) | 0 bits | Theta(sqrt(N/d_0)) | None needed | None |
| Adiabatic, gap-informed | n/2 bits of A_1 | Theta(sqrt(N/d_0)) | Classical precomp (NP-hard) | A_1 estimation |
| Adiabatic, C bits | C bits of A_1 | T_inf * 2^{n/2-C} | Partial precomp | Partial A_1 |
| Adiabatic, uninformed | 0 bits | Omega(N/sqrt(d_0)) | None | Full A_1 gap |
| Adiabatic, adaptive | 0 classical bits | Theta(sqrt(N/d_0)) | O(n) quantum measurements | None (circumvented) |
| Adiabatic, modified H | 0 bits | Omega(N/sqrt(d_0)) | Cannot circumvent | Rank-one no-go (Exp 12) |
| Quantum A_1 estimation | — | O(2^{n/2} poly(n)) | Phase estimation | — |
| Classical A_1 estimation | — | Omega(2^n) | Query model | Exp 13 lower bound |

To write this theorem:
1. Import the no-go result from Exp 12 (Theorem 5: within rank-one instance-independent design, A_1 barrier unbreakable). Cite it; do not re-derive.
2. Import the quantum-classical separation from Exp 13 (Theorems 2-5: quantum O(2^{n/2}), classical Omega(2^n) for A_1 estimation at precision 2^{-n/2}). Cite it; do not re-derive.
3. Import the structured tractability story from Exp 08 (Propositions 8-12: for bounded-treewidth families, A_1 computable in poly time). Add a remark: the model comparison table changes qualitatively when A_1 is tractable — the "NP-hard precomputation" row drops to polynomial, making gap-informed adiabatic practical.
4. Write a unified theorem statement that captures the complete landscape. State all assumptions, cite all sources, and discuss the implications.

**Scope note:** These results apply specifically to ground-state finding of diagonal Hamiltonians (the AQO setting). For other computational tasks (energy estimation, full spectrum reconstruction, thermal state preparation), spectral information may be necessary even in the circuit model. The synthesis theorem should state this scope limitation explicitly.

**Why this is novel:** No single experiment currently states the full picture. The paper proves hardness (Ch 8). Exp 10 proves model separation. Exp 12 proves the barrier is structural. Exp 13 proves the quantum-classical estimation gap. Exp 08 identifies when the barrier dissolves. The synthesis theorem says: "Here is the complete computational landscape for adiabatic ground-state finding, and here is exactly what each model can and cannot achieve."

### Gap 2: Progress on Conjecture 5 (Continuous-Time A_1 Barrier)

Conjecture 5 states: for any continuous-time rank-one algorithm with controls f(t), g(t) chosen without knowledge of A_1, the runtime is Omega(N/sqrt(d_0)).

This is explicitly open. The experiment cites evidence for (Farhi et al. 2008) and against (diabatic protocols, higher-rank drivers).

**Concrete targets (in order of decreasing ambition):**

(a) **Prove Conjecture 5 for monotone controls (highest-value partial result).** Prove the Omega(N/sqrt(d_0)) lower bound for all continuous-time rank-one algorithms where f(t) and g(t) are monotone (f decreasing, g increasing — the standard adiabatic regime). This restriction excludes the "diabatic protocols" and "non-adiabatic fast passage" escape hatches cited as evidence against the full conjecture, making it more likely provable. It would establish that monotone control functions cannot avoid the A_1 barrier even with non-adiabatic speeds, and the escape must come from qualitatively different control strategies (non-monotone, higher-rank, etc.).

(b) **Prove a weaker version.** For example: prove that any rank-one algorithm achieving T = O(sqrt(N/d_0)) must have its control functions depend on A_1 (or on information equivalent to Omega(n/2) bits about the spectrum). This is weaker than the full conjecture but still novel and connects to the communication complexity framework.

(c) **Document the obstruction.** If (a) and (b) fail, write a precise analysis of WHY the conjecture is hard to prove. What technique would be needed? Where does the Farhi et al. argument break for general controls? What is the specific barrier to extending their Theorem 1 beyond the specific spectral structure they consider? This documented obstruction should go in proof.md as a "Remark: Difficulty of Conjecture 5" section.

**Important constraint:** Do NOT claim to prove the full conjecture unless the proof is airtight. A careful partial result or documented obstruction is worth far more than a flawed proof of the full statement. The experiment's integrity depends on honesty here.

### Gap 3: Precision-Aware Model Comparison (Connection to Exp 13)

The bit-runtime tradeoff (Theorem 7) says each bit of A_1 halves adiabatic runtime: T(C) = T_inf * 2^{n/2-C}. Experiment 13 says estimating A_1 to precision 2^{-n/2} costs O(2^{n/2}) quantumly and Omega(2^n) classically.

These two results together imply a clean corollary that is not currently stated:

**Proposition (Quantum Pre-Computation Tradeoff):** A quantum computer can estimate A_1 to sufficient precision for optimal adiabatic scheduling in time O(2^{n/2} * poly(n)) — exactly the same order as the optimal adiabatic runtime itself. Therefore, quantum estimation of A_1 followed by informed adiabatic evolution gives total runtime O(2^{n/2} * poly(n)) = O(sqrt(N/d_0) * poly(n)), matching Durr-Hoyer (up to poly factors) but via a fundamentally different computational path.

**Contrast with classical:** Classical A_1 estimation costs Omega(2^n), so classical pre-computation followed by adiabatic evolution gives total runtime Omega(2^n) + O(sqrt(N/d_0)) = Omega(N) — worse than brute-force search.

Write this as a clean proposition with proof (chain Theorem 7 and Exp 13's results). Discuss the deeper implication: **the quantum-classical gap in A_1 estimation is exactly the computational gap between the circuit and adiabatic models.** The "information cost" of the adiabatic approach equals precisely the quantum speedup that the circuit model provides for free. This is not a coincidence — it reflects the structural fact that quantum search and quantum estimation share the same sqrt(N) scaling from amplitude amplification. State this structural connection explicitly.

### Gap 4: Chapter 9 Integration Plan

The README's Chapter 9 outline lists sections for Exps 02, 04, 05, 06, 07, and a synthesis ("The Ignorance Taxonomy"). Experiment 10's model-separation results are NOT currently listed in any Chapter 9 section.

**Concrete tasks:**

1. Read the Chapter 9 outline in the main `README.md` (around line 621). Chapter 9 currently has sections for: Separation Theorem (Exp 04), Partial Information (Exp 07), Robust Schedules (Exp 02), Adaptive Schedules (Exp 05), Measure Condition (Exp 06), and The Ignorance Taxonomy (synthesis). Determine where Exp 10's results belong. The most natural placement is as the **capstone section** of Chapter 9, after the Ignorance Taxonomy. The model comparison says: "Having characterized how information determines runtime within the adiabatic model (taxonomy), we now ask: is this information barrier fundamental? Answer: no — the circuit model bypasses it entirely."

2. Write a brief Chapter 9 insertion outline (similar to the one in Exp 08's todo.md). This should specify:
   - Which theorems from proof.md become which propositions/theorems in Chapter 9
   - How the model comparison table integrates with the Ignorance Taxonomy
   - Where the synthesis theorem (Gap 1) fits
   - Where the precision comparison (Gap 3) fits

3. Add this outline to a new `todo.md` file in the experiment directory.


## Deliverables and Quality Standards

### What to produce:

1. **New propositions/theorems in `proof.md`**: create a new Part X (after the existing Part IX) for the synthesis theorem. The existing Parts I-IX are complete; do NOT modify them. The synthesis theorem imports results from Exp 08, 12, 13 by citation — do not re-derive. The precision corollary (Gap 3) fits naturally as a new section within or after Part VIII (Unified Information-Runtime Landscape).

2. **Numerical verification**: for any new quantitative claim, add verification to `lib/verify.py` or create a new script. Run it and confirm output matches.

3. **New `todo.md`**: create this file following the experiment conventions (`## Plans`, `## Progress`, `## Findings`). Document all open threads, including Conjecture 5 status.

4. **Updated `main.md`**: update the Results table, Novelty Assessment, and Open Questions sections. Add connection to experiments 08, 12, 13. If any open questions are now resolved, mark them.

5. **Lean updates (optional but valuable)**: if the synthesis theorem or precision corollary can be stated in Lean (even axiomatized with cross-references), add to `lean/InformationTheoretic.lean`.

### Quality standards (from CLAUDE.md):

- Every sentence must carry information. No filler.
- State results with explicit bounds, clear dependencies, honest limitations.
- Proof strategy stated upfront. Decompose into lemmas matching logical moves.
- Do not signal technique ("to provide intuition"). Just provide it.
- Avoid grandesque statements. Keep sentences small and direct.
- All math must follow correct LaTeX conventions.
- No non-ASCII characters.
- Avoid bullet points in prose (lists are fine in structured sections like tables).

### Correctness requirements:

- Every new proposition must have a complete proof or explicit citation to a proved result in another experiment.
- When importing results from other experiments, cite the exact proposition/theorem number and experiment directory. Do NOT re-derive.
- The synthesis theorem must state all assumptions precisely. Each row of the model comparison table must have a cited source.
- If Conjecture 5 progress yields a partial result, state the restricted class precisely. If it yields a documented obstruction, state the obstruction precisely.
- Error bounds must be explicit (no hidden constants, no "poly(n)" without specifying what polynomial).


## Execution Strategy

1. Read all files in `src/experiments/10_information_theoretic/` first.
2. Read `main.md` files of experiments 08, 12, 13.
3. Read `CLAUDE.md` for style guidelines.
4. Create `todo.md` with a plan before starting any proof work.
5. Start with Gap 3 (precision corollary) — this is the quickest win and requires only chaining existing results.
6. Then do Gap 1 (synthesis theorem) — this is the highest-value target and requires careful integration of cross-experiment results.
7. Then do Gap 4 (Chapter 9 outline) — this provides narrative closure.
8. Attempt Gap 2 (Conjecture 5) only after Gaps 1, 3, 4 are done. Prioritize proving Conjecture 5 for monotone controls (target (a)) or documenting the obstruction precisely (target (c)). Do not overcommit — a documented obstruction stating where Farhi et al.'s technique breaks for general controls is a valid contribution.
9. After all work: re-read proof.md end-to-end for consistency. Ensure tables are updated in main.md.


## Success Criteria

The experiment is COMPLETE if:
- The synthesis theorem (Gap 1) is stated and proved (by citation-chaining)
- The precision corollary (Gap 3) is stated and proved
- A todo.md exists with documented status of all threads including Conjecture 5
- main.md is updated with cross-experiment connections
- The Chapter 9 insertion outline exists
- All numerics pass

The experiment achieves NOVELTY if:
- The synthesis theorem presents a unified landscape not found in any single prior source (paper, Guo-An, or individual experiments)
- The precision corollary reveals a new structural insight: quantum estimation cost matches quantum search cost, making the "information gap" exactly the "quantum speedup gap"
- Any progress on Conjecture 5 (even a restricted-class proof or a documented obstruction) is novel
- The results could form the capstone section of Chapter 9 with no additional work

Note: Conjecture 5 outcomes may be negative results (documented obstructions). These count as valid contributions if the obstruction is genuine, precisely stated, and reveals why extending Farhi et al.'s argument to general continuous-time controls is fundamentally difficult.


## What NOT to do

- Do NOT re-derive Theorems 1-7 or Propositions 6-8. They are correct and verified.
- Do NOT re-derive results from other experiments. Import by citation.
- Do NOT attempt the full Conjecture 5 proof unless Gaps 1, 3, 4 are done.
- Do NOT create new experiment directories or restructure the project.
- Do NOT modify files outside `src/experiments/10_information_theoretic/`.
- Do NOT write vague "future work" sections. Every claim must be precise.
- Do NOT introduce new notation without defining it. Check proof.md's existing notation.
- Do NOT conflate the thesis's Chapter 9 outline (in README.md) with the experiment's internal structure. The Chapter 9 insertion outline goes in the experiment's todo.md, not in README.md.
