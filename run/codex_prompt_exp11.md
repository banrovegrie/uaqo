# Complete Experiment 11 (Schedule Optimality)

## Context

You are working on a master's thesis on Unstructured Adiabatic Quantum Optimization. The thesis extends the paper "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736). Read `CLAUDE.md` for project guidelines, style, and structure.

Experiment 11 lives in `src/experiments/11_schedule_optimality/`. Read every file in this directory before doing anything: `main.md`, `proof.md`, `lib/verify_extensions.py`, and the Lean files in `lean/`. Also read `src/experiments/README.md` and `src/experiments/CLAUDE.md` for experiment conventions.

The central question: **How does the paper's optimal schedule relate to Guo-An (2025)'s variational framework?** The answer (already established): both frameworks yield T = O(sqrt(NA_2/d_0)/epsilon) for the paper's Hamiltonian class (same asymptotic scaling, different constant factors); the paper's gap has flatness alpha=1 (boundary case for Guo-An's measure condition); the JRS bound uses C^2 which is smaller than the RC integral constant I when c_L > 1.

**Critical context: neighboring experiments.** Before doing any work, also read the `main.md` files of:
- `src/experiments/06_measure_condition/main.md` -- establishes alpha=1 boundary and the scaling spectrum T = Theta(1/Delta_*^{3-2/alpha})
- `src/experiments/07_partial_information/main.md` -- interpolation theorem T(epsilon) = T_inf * Theta(max(1, epsilon/delta_{A_1}))
- `src/experiments/08_structured_tractability_v2/main.md` -- structured families where A_1 is tractable
- `src/experiments/10_information_theoretic/main.md` -- model separation and bit-runtime tradeoff


## What Is Already Done (DO NOT REDO)

Status: RESOLVED. All 4 conjectures proved. Theorems A--H + Extensions complete in proof.md. Lean verification with 2 axioms only. 5 numerical claims verified.

**Completed results:**
- Theorem A: Measure condition holds with C <= 3A_2/(A_1(A_1+1)) + 30(1-s_0)/Delta
- Theorem B: Grover case C_Grover = 1 for all N >= 2 (axiom-free Lean proof)
- Theorem C: Both p=2 (RC) and p=3/2 (JRS) achieve T = O(sqrt(NA_2/d_0)/epsilon)
- Theorem D: Exact Grover integral I_exact = N/sqrt(N-1) * arctan(sqrt(N-1))
- Extension E: Constant comparison C^2/I -> 1089/1806 ~ 0.603 for Grover as N -> infinity
- Extension F: Measure condition classification by gap flatness alpha (alpha <= 1 holds, alpha > 1 fails)
- Extension G: Structural alpha=1 for the paper's Hamiltonian class
- Extension H: Framework comparison RC vs JRS across gap geometries
- All 4 conjectures: PROVED


## What Is Missing (THE ACTUAL WORK)

The core results are complete but the experiment is missing synthesis, integration, and one concrete extension that would add genuine novelty beyond connecting two known frameworks.

### Gap 1: Schedule Selection Under Partial Information (Connection to Exps 07 + 10)

The experiment proves that both p=2 and p=3/2 schedules achieve the same asymptotic runtime when A_1 is fully known. But what happens when A_1 is only partially known?

**Concrete target:**

Proposition: When A_1 is known to precision epsilon, the paper's locally-adapted schedule (p=2, using ds/dt proportional to g(s)^2) achieves runtime T(epsilon) = T_inf * Theta(max(1, epsilon/delta_{A_1})) (import from Exp 07, verify this claim by reading Exp 07's main.md first). For Guo-An's p=3/2 schedule, which needs g_min and the measure condition constant C but not the full gap profile, what is the corresponding partial-information runtime?

Specifically:
1. The RC schedule (p=2) needs s* to precision delta_s to correctly locate the window. Error in A_1 propagates to error in s* via ds*/dA_1 = 1/(A_1+1)^2. This is already characterized by Exp 07.
2. The JRS schedule (p=3/2) needs g_min and C (the measure condition constant). How sensitive is the p=3/2 runtime to errors in these quantities? Derive the error propagation: if C is estimated to precision delta_C, what is the resulting runtime degradation?
3. Compare: which schedule degrades more gracefully under partial information? This would tell a practitioner: "If you have coarse A_1 knowledge, use schedule X; if you have precise knowledge, use schedule Y."

Write this as a proposition in proof.md with proof. This connects Exp 11 (schedule optimality) to Exp 07 (partial information) in a way neither experiment currently does.

### Gap 2: Quantitative Schedule Comparison for Structured Families (Connection to Exp 08)

Extension E shows C^2/I ~ 0.603 for Grover. For structured families where A_1 is tractable (Exp 08), the spectral parameters are different.

**Concrete target:**

Compute C and I (or their ratio) for at least one structured family from Exp 08:
1. Read the ferromagnetic Ising results from Exp 08 (Prop 13). Extract the spectral parameters (A_1, A_2, Delta, s_0) for a concrete small instance.
2. Evaluate C and I for this instance using the formulas from Theorems A and C.
3. Compare: is C^2/I larger or smaller than the Grover ratio 0.603? What does this tell us about which schedule framework is better for structured instances?

This can be a computational remark rather than a theorem. Add the computation to `lib/verify_extensions.py` and state the result as a Remark in proof.md.

### Gap 3: Chapter 9 Integration Plan

The experiment's results should map to a specific section in Chapter 9. Currently there is no integration plan.

**Concrete tasks:**

1. Read the Chapter 9 outline in `README.md` (around line 685, "Measure Condition and Scaling" section, which sources Exp 06). Experiment 11 extends Exp 06's results by connecting to Guo-An's framework. The natural placement is as a **subsection within or immediately after** the Measure Condition section.

2. Write a Chapter 9 insertion outline specifying:
   - Which theorems from proof.md become Chapter 9 content
   - How the RC vs JRS comparison integrates with the measure condition discussion
   - Where the partial-information schedule comparison (Gap 1) fits
   - What can be deferred to remarks or appendices

3. Add this outline to a new `todo.md` file in the experiment directory.

### Gap 4: Open Question Investigation (Optional)

Three open questions from main.md. Attempt only if Gaps 1--3 are done:

(a) **Explicit JRS constant**: compute the exact JRS error functional constant for the paper's Hamiltonian and compare to the RC constant. This would make Extension E's comparison quantitatively precise (not just asymptotic).

(b) **Non-power-law schedules**: for a specific non-power-law schedule (e.g., exponential slowdown near s*), compute the runtime and compare to p=2 and p=3/2. This would test whether the power-law family is truly optimal.


## Deliverables and Quality Standards

### What to produce:

1. **New propositions in `proof.md`**: append after Extension H. The partial-information schedule comparison (Gap 1) is the primary new result. The structured-family computation (Gap 2) is a Remark.

2. **Updated `lib/verify_extensions.py`**: add numerical verification for any new claims.

3. **New `todo.md`**: create with Plans, Progress, Findings sections. Document all open threads.

4. **Updated `main.md`**: add cross-experiment connections. Update Open Questions to reflect any progress.

### Quality standards (from CLAUDE.md):

- Every sentence must carry information. No filler.
- State results with explicit bounds and dependencies.
- All math must follow correct LaTeX conventions.
- No non-ASCII characters.

### Correctness requirements:

- When importing from other experiments, cite exact theorem/proposition numbers.
- Error propagation must be explicit (how delta_C affects T for p=3/2).
- Numerical comparisons must be verified in lib/.


## Execution Strategy

1. Read all files in the experiment directory.
2. Read main.md of Exps 06, 07, 08, 10.
3. Read `CLAUDE.md`.
4. Create `todo.md`.
5. Start with Gap 1 (partial-information schedule comparison) -- highest novelty.
6. Then Gap 2 (structured-family computation) -- quick computational remark.
7. Then Gap 3 (Chapter 9 outline).
8. Gap 4 only if time permits.
9. Re-read proof.md for consistency.


## Success Criteria

The experiment is COMPLETE if:
- The partial-information schedule comparison (Gap 1) is stated and proved
- The Chapter 9 insertion outline exists
- todo.md exists with documented status
- All numerics pass

The experiment achieves NOVELTY if:
- The partial-information comparison reveals a practical recommendation (which schedule degrades more gracefully)
- The structured-family comparison shows a quantitative difference from the Grover case
- The results integrate into Chapter 9 as the "which schedule to use" practical guidance


## What NOT to do

- Do NOT re-derive Theorems A--H. They are correct and verified.
- Do NOT re-derive results from other experiments. Import by citation.
- Do NOT modify files outside `src/experiments/11_schedule_optimality/`.
- Do NOT write vague "future work" sections.
- Do NOT introduce new notation without checking proof.md's existing conventions.
