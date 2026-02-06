# Complete Experiment 08 (Structured Tractability v2)

## Context

You are working on a master's thesis on Unstructured Adiabatic Quantum Optimization. The thesis extends the paper "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736). Read `CLAUDE.md` for project guidelines, style, and structure.

Experiment 08 lives in `src/experiments/08_structured_tractability_v2/`. Read every file in this directory before doing anything: `main.md`, `proof.md`, `todo.md`, and all scripts in `lib/`. Also read `src/experiments/README.md` and `src/experiments/CLAUDE.md` for experiment conventions.

The central question of this experiment: **When is A_1 easy to compute?** The paper proves A_1 is #P-hard for general Hamiltonians. This experiment characterizes the tractability boundary by connecting A_1 to partition-function complexity.


## What Is Already Done (DO NOT REDO)

12 propositions are proved in `proof.md`. All numerics verified in `lib/`. The "boundary-setting" work is complete:

- Props 1-2: Conjectures 1 (false) and 2 (vacuous) resolved with counterexamples
- Prop 3: Sufficient condition (poly levels + known d_k + known E_k)
- Prop 4: CSP hardness (#P-hard counting implies #P-hard A_1)
- Props 5-6: Grover sweet spot + Conjecture 3 false in both directions
- Prop 7: Hamming distance (A_1 depends only on n)
- Prop 8: Bounded treewidth exact A_1 via variable-elimination DP
- Prop 9: Monte Carlo coarse approximation when E_0 is known
- Props 10-12: Partition-function bridge (A_1 from Z(t) or Z(beta) without d_0, oracle reduction)
- Partition-function identities (Laplace + ordinary GF) proved as structural lemma

This is solid but it is all **boundary-setting**. The experiment is NOT yet novel enough.


## What Is Missing (THE ACTUAL WORK)

Read `todo.md` carefully. The unchecked items and the "Missing (needed for novelty)" section define exactly what remains. There are three gaps, in decreasing order of importance:

### Prerequisite: Structured Family Selection (todo.md Section D)

Before committing to a specific theorem, write a 1-page family-selection memo justifying your choice. Section D of todo.md lists five candidates (bounded treewidth CSPs, ferromagnetic Ising, XOR-SAT, Horn-SAT, submodular energies) with selection criteria. Your memo should state: the chosen family, why it has a nontrivial partition-function story, what the known Z results are, the target precision, and the likely theorem statement. This memo goes in the `notes/` directory as `family_selection.md`.

### Gap 1: A Nontrivial Positive Tractability Theorem for a Natural Broad Family

Prop 8 (bounded treewidth) is a positive result, but it is essentially "if you can compute Z(t) exactly, you can compute A_1." We need a result where Z is not exactly computable but *approximately* computable, and that approximation suffices for A_1.

**Concrete target (pick ONE and do it completely):**

(a) **Ferromagnetic Ising with consistent external fields.** The Jerrum-Sinclair FPRAS gives multiplicative approximation to Z(beta). Combined with Prop 11 or 12, this should yield additive A_1 approximation in randomized poly time. Write this as a clean theorem (Prop 13 or similar) with:
   - Precise statement: input model, what "ferromagnetic with consistent fields" means for the diagonal Hamiltonian, the FPRAS guarantee you invoke (cite Jerrum-Sinclair 1993), and the resulting A_1 approximation quality
   - Proof: chain the FPRAS through Props 10-12, handling the error propagation carefully (multiplicative Z-error vs additive A_1-error)
   - Discussion: why this is nontrivial (exact A_1 may still be #P-hard for this family since counting is hard, but approximate A_1 is easy via the partition-function route)

(b) **XOR-SAT / linear codes over GF(2).** Counting solutions to XOR-SAT is in P (Gaussian elimination gives |solution space| = 2^{n-rank}). The energy function E(x) = number of violated XOR clauses gives a Hamiltonian whose partition function Z(t) can be computed exactly in poly time (since the weight enumerator of a linear code is computable). Derive exact A_1 from this. Write as a theorem with proof. This is cleaner than (a) but less impressive because it does not use approximation.

(c) **Antiferromagnetic 2-spin systems in the uniqueness regime.** Weitz (2006) and subsequent work give deterministic FPTAS for Z in the uniqueness regime on bounded-degree graphs. If the corresponding Hamiltonian falls within this regime, derive A_1 approximation.

Pick whichever you can do most rigorously. Do NOT attempt all three. One clean, complete theorem is worth more than three sketches.

### Gap 2: A Nontrivial Negative/Boundary Theorem

We need a result showing that for some structured family, approximating A_1 is hard. This must NOT be a restatement of the paper's interpolation reduction (Prop 4 already captures that).

**Before attempting a proof, complete the groundwork in todo.md section B0:**

1. Fix the input model: diagonal k-local Hamiltonians, bounded weights, bit complexity, and what the input/oracle access is.
2. Fix the approximation notion: additive precision eta(n) (candidates: eta = 2^{-n/2} or eta = 1/poly(n)).
3. Write a conjecture/theorem template: "If A_1 is polytime computable for all instances in family F, then ..."

**Then attempt one of these strategies (from todo.md section B1):**

(a) **Reverse partition-function bridge.** Prove that for antiferromagnetic Ising on general graphs (or some specific hard regime for Z), approximating A_1 to inverse-polynomial additive accuracy is #P-hard (or NP-hard under randomized reductions). The argument should go through Props 10-12 in reverse: if A_1 approximation were easy, it would give Z approximation, contradicting known hardness of Z.

(b) **Signal amplification reduction.** Try decision-to-A_1 "signal amplification" producing a robust Theta(1) separation in A_1 at inverse-poly precision. Or try promise reductions (satisfiable vs far-from-satisfiable) so that E_0 = 0 and the signal is stable.

(c) **Barrier lemma.** Prove that any method for A_1 approximation at precision eta = 2^{-n/2} (the schedule-relevant regime) necessarily requires information equivalent to low-temperature partition-function evaluation, which is known to be hard for general models.

**If the proof attempt fails (todo.md section B2):** Document the obstruction precisely. State what was tried, where it breaks, and why. A documented obstruction that reveals a genuine barrier IS a publishable result and a valid outcome for this gap. Add findings to todo.md under section B2 and to proof.md as a "Remark" or "Negative Result" section.

### Gap 3: Precision-Aware Bridge to Chapter 9

This is the "so what" of the experiment: connecting the tractability results to what AQO actually needs.

**Concrete tasks:**

1. Extract from the paper (Section 4, around the definition of delta_s and the schedule construction) the required A_1 precision for schedule correctness. Restate it in the experiment's notation. The key quantity is: what additive error eta in A_1 is tolerable for the optimal schedule to remain near-optimal (say within a constant factor of T_inf)?

2. For the structured family from Gap 1, determine whether the achievable A_1 precision (inverse-poly additive) is sufficient for near-optimal schedules, or whether it only gives a constant-factor schedule. State this as a proposition or remark.

3. Write the "precision landscape" paragraph: coarse A_1 (eta = 1/poly(n)) corresponds to moderate-temperature partition functions (Prop 10-12 remarks already hint at this); schedule-relevant A_1 (eta = 2^{-n/2}) corresponds to low-temperature partition functions. This is the information-theoretic content of the experiment.

This does NOT need to be a deep theorem. A clean, precise discussion with one proposition connecting precision to temperature regime is sufficient.


## Deliverables and Quality Standards

### What to produce:

1. **New propositions in `proof.md`**: append after Prop 12. Follow the exact style of existing propositions (statement, proof, remarks, sanity checks). Number sequentially.

2. **Numerical verification**: for any new quantitative claim, add verification to `lib/verify_a1.py` or create a new script in `lib/`. Run it and confirm output matches.

3. **Updated `todo.md`**: check off completed items, add new findings to the Findings section, update the Progress log with dated entries.

4. **Updated `main.md`**: update the Results table, add new results to "Key Conclusions", update "Remaining Open Questions" to remove anything resolved and add any new open questions.

5. **Updated Chapter 9 insertion outline** in `todo.md`: the outline already exists (lines 158-169 of todo.md). Integrate the new results into this existing draft outline -- do not create a new one from scratch.

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

- Every new proposition must have a complete proof (no "the proof follows by standard arguments" unless the standard argument is named and referenced).
- Every quantitative claim must be numerically verified.
- Error bounds must be explicit (no hidden constants). In particular, every new proposition must make the following error parameters explicit where relevant: energy normalization scale, minimum excited energy Delta_min, mass near ground state d_0/N, and any other problem-specific error drivers (see unchecked item in todo.md section A1).
- Assumptions must be stated precisely (input model, approximation notion, promise).
- If invoking an external result (Jerrum-Sinclair, Weitz, etc.), state exactly what guarantee you use, with a precise citation.
- If a proof attempt fails, document the failure mode precisely in todo.md under section B2. A documented obstruction is more valuable than a false claim.


## Execution Strategy

1. Read all files in `src/experiments/08_structured_tractability_v2/` first.
2. Read `CLAUDE.md` for style guidelines.
3. Start with Gap 1 (positive theorem) -- this is the highest-value target.
4. Then do Gap 3 (precision bridge) -- this is the easiest and gives narrative closure.
5. Attempt Gap 2 (negative theorem) only if time permits -- this is high-risk.
6. For each gap: write the proposition in proof.md, write/update verification code, update todo.md and main.md.
7. After all work: re-read proof.md end-to-end for consistency and flow. Ensure the Summary Table at the bottom is updated.

## Success Criteria

The experiment is COMPLETE if:
- At least one new substantive theorem beyond Props 1-12 (Gap 1 or Gap 2)
- The precision-aware bridge is written (Gap 3, even as a remark/discussion)
- All files are updated consistently
- All numerics pass
- The "Missing (needed for novelty)" section in todo.md can be replaced with "Resolved" entries

The experiment achieves NOVELTY if:
- The positive structured-family theorem (Gap 1) is genuinely new (not in the paper, not in Guo-An 2025)
- The precision bridge (Gap 3) provides a new interpretation of the paper's information barrier
- The results could form Section 9.x of the thesis with no additional work

Note: Gap 2 outcomes may be negative results (documented obstructions with barriers). These count as valid completions if the obstruction is genuine, precisely stated, and reveals structural insight about why A_1 hardness cannot be easily reversed through the partition-function bridge.

## What NOT to do

- Do NOT re-derive or re-prove Props 1-12. They are correct and verified.
- Do NOT attempt the "no-go theorem" (todo.md section B) unless Gaps 1 and 3 are fully done.
- Do NOT create new experiment directories or restructure the project.
- Do NOT modify files outside `src/experiments/08_structured_tractability_v2/`.
- Do NOT write vague "future work" sections. Every claim must be precise.
- Do NOT introduce new notation without defining it. Check proof.md's existing notation section.
