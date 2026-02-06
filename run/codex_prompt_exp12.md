# Complete Experiment 12 (Circumventing the Barrier)

## Context

You are working on a master's thesis on Unstructured Adiabatic Quantum Optimization. The thesis extends the paper "Unstructured Adiabatic Quantum Optimization: Optimality with Limitations" (arXiv:2411.05736). Read `CLAUDE.md` for project guidelines, style, and structure.

Experiment 12 lives in `src/experiments/12_circumventing_barrier/`. Read every file in this directory before doing anything: `main.md`, `proof.md`, and `lib/ancilla_spectrum.py`. Also read `src/experiments/README.md` and `src/experiments/CLAUDE.md` for experiment conventions.

The central question: **Can modified Hamiltonians (ancilla qubits, multi-segment paths) make s* independent of the problem spectrum?** The answer (already established): No, within rank-one instance-independent design. The A_1 barrier is unbreakable under these assumptions.

**Critical context: neighboring experiments.** Before doing any work, read the `main.md` files of:
- `src/experiments/05_adaptive_schedules/main.md` -- adaptive measurement circumvents the barrier within adiabatic model
- `src/experiments/10_information_theoretic/main.md` -- circuit model bypasses the barrier entirely
- `src/experiments/13_intermediate_hardness/main.md` -- quantum estimation of A_1 at 2^{-n/2}
- `src/experiments/08_structured_tractability_v2/main.md` -- structured families where A_1 is tractable


## What Is Already Done (DO NOT REDO)

Status: COMPLETE. All 5 conjectures resolved. 5 main theorems proved. Numerical verification comprehensive (822-line Python script). No Lean formalization.

**Completed results:**
- Theorem 1 (Product State Invariance): product ancilla extension leaves crossing at s* = A_1/(A_1+1) exactly
- Theorem 2 (Universality of Uniform Superposition): the uniform superposition is the unique state (up to phases) for which weights depend only on eigenvalues/degeneracies
- Theorem 3 (Coupled Ancilla): fixed coupling V cannot make A_1^eff constant across instances
- Theorem 4 (Multi-Segment Rigidity): multi-segment paths also locked to A_1 by instance-independence
- Theorem 5 (No-Go): within rank-one instance-independent design, A_1 barrier is unbreakable
- Part VII (Escape Routes): detailed analysis of what COULD work (higher-rank H_0, time-dependent couplings, non-instance-independent, adaptive, non-adiabatic)
- Corollary: non-adiabatic oscillation faces the same barrier
- 6 open questions documented

The no-go theorem is strong. The escape routes analysis is thorough. The main gaps are in pushing beyond the no-go boundary.


## What Is Missing (THE ACTUAL WORK)

### Gap 1: Investigate the Most Promising Escape Route (Higher-Rank H_0)

Part VII identifies higher-rank initial Hamiltonians as the primary escape route. Currently this is only discussed qualitatively. A concrete result here would be the experiment's strongest novel contribution.

**Concrete target:**

Consider H_0 = -P where P is a rank-k projector (k > 1) onto a subspace that includes the uniform superposition. The secular equation changes: instead of the rank-one equation 1/(1-s) = (1/N) sum d_j/(sE_j - lambda), we get a k-dimensional eigenvalue problem.

(a) **For k=2**: take H_0 = -(|psi_0><psi_0| + |phi><phi|) where |phi> is orthogonal to |psi_0> and has specified overlaps with the computational basis. Derive the crossing structure. Does the crossing position still depend on A_1, or can |phi> be chosen to shift it?

(b) **If the crossing still depends on A_1 for k=2**: prove this as a proposition extending Theorem 5. This would strengthen the no-go by showing that small rank increases do not help.

(c) **If the crossing can be made A_1-independent for some k**: prove this as a positive circumvention result. Determine the minimum rank k needed and the conditions on the projector subspace.

(d) **If the analysis is inconclusive**: document the obstruction. What makes the higher-rank case harder to analyze? What is the generalized secular equation? Where does the argument from Theorem 2 (uniqueness of uniform superposition) break?

Pick whichever outcome the mathematics supports. Do NOT force a result.

### Gap 2: Lean Formalization of Core Theorems

Unlike experiments 04, 06, 07, and 11, this experiment has no Lean formalization. The no-go theorem (Theorem 5) and its key ingredient (Theorem 2, universality) are strong candidates for formalization.

**Concrete target:**

Create a `lean/` directory with:
1. Basic definitions: spectral parameters, crossing position, weights w_k = d_k/N
2. Theorem 2 (Universality): encode the STATEMENT that uniform overlaps are the unique choice giving spectrum-independent weights. The theorem is already fully proved in proof.md; the task here is Lean encoding. The permutation argument is expressible in Lean.
3. Theorem 5 (No-Go): encode the STATEMENT of the composition (Theorems 1--4 imply 5). Axiomatize the component theorems if full proofs are too complex to encode.

Even a partial formalization (axiomatized component theorems, proved composition) adds value. The Lean files should follow the conventions of the existing formalization in `src/lean/`. Note: the experiment currently has NO Lean files at all, so this creates new infrastructure from scratch.

### Gap 3: Cross-Experiment Synthesis (What CAN Circumvent the Barrier?)

The experiment proves what CANNOT circumvent the barrier. Combined with other experiments, we can now characterize what CAN:
- Exp 05: adaptive measurement circumvents within adiabatic model
- Exp 10: circuit model (Durr-Hoyer) bypasses entirely
- Exp 13: quantum A_1 estimation achieves O(2^{n/2})
- Exp 08: structured families make A_1 tractable classically

**Concrete target:**

Write a "Circumvention Landscape" proposition or remark (in proof.md, after Part VII) that states:

Within AQO for unstructured ground-state finding, the A_1 barrier can be circumvented by:
1. Leaving the adiabatic model entirely (circuit model, 0 bits, Theta(sqrt(N/d_0))) -- cite Exp 10, Theorem 2
2. Adaptive quantum measurement during evolution (0 classical bits, O(n) measurements) -- cite Exp 05
3. Quantum pre-estimation of A_1 (O(2^{n/2} poly(n)) total time) -- cite Exp 13, Theorem 2
4. Exploiting problem structure where A_1 is classically tractable -- cite Exp 08

And CANNOT be circumvented by:
5. Product ancilla extensions (Theorem 1)
6. Non-uniform initial states (Theorem 2)
7. Fixed coupled ancillas (Theorem 3)
8. Multi-segment adiabatic paths (Theorem 4)
9. Any rank-one instance-independent Hamiltonian modification (Theorem 5)

This creates a clean "what works / what doesn't" summary.

### Gap 4: Chapter 9 Integration Plan

**Concrete tasks:**

1. Read the Chapter 9 outline in `README.md`. The natural placement for Exp 12 is after the Adaptive Schedules section (Exp 05) or as part of the capstone synthesis. The narrative: "Adaptive measurement circumvents the barrier (Exp 05). Can Hamiltonian modifications achieve the same? No (Exp 12)."

2. Write a Chapter 9 insertion outline specifying which theorems map to which propositions.

3. Add to `todo.md`.


## Deliverables and Quality Standards

### What to produce:

1. **New results in `proof.md`**: higher-rank investigation (Gap 1) as a new Part VIII or extension of Part VII. Circumvention landscape (Gap 3) as a closing Remark or Proposition.

2. **Lean formalization** (Gap 2): create `lean/` directory with at minimum Theorem 2 and Theorem 5 statements. Follow `src/lean/` conventions.

3. **New `todo.md`**: create with Plans, Progress, Findings sections.

4. **Updated `main.md`**: add cross-experiment connections. Update Open Questions.

5. **Updated `lib/ancilla_spectrum.py`**: add numerical experiments for higher-rank H_0 if Gap 1 produces results.

### Quality standards (from CLAUDE.md):

- Every sentence must carry information. No filler.
- State results with explicit bounds and dependencies.
- All math must follow correct LaTeX conventions.
- No non-ASCII characters.

### Correctness requirements:

- Higher-rank analysis (Gap 1) must be mathematically rigorous or honestly documented as inconclusive.
- Lean formalization must build without errors. Axiomatized results must be clearly labeled.
- Cross-experiment citations must reference exact theorem numbers.


## Execution Strategy

1. Read all files in the experiment directory.
2. Read main.md of Exps 05, 08, 10, 13.
3. Read `CLAUDE.md`.
4. Create `todo.md`.
5. Start with Gap 3 (circumvention landscape) -- quickest, highest-value synthesis.
6. Then Gap 1 (higher-rank investigation) -- highest novelty.
7. Then Gap 4 (Chapter 9 outline).
8. Gap 2 (Lean) only if time permits after Gaps 1, 3, 4.
9. Re-read proof.md for consistency.


## Success Criteria

The experiment is COMPLETE if:
- The circumvention landscape (Gap 3) is stated with full cross-experiment citations
- The higher-rank investigation (Gap 1) produces either a new theorem or a documented obstruction
- todo.md and Chapter 9 outline exist
- All numerics pass

The experiment achieves NOVELTY if:
- The higher-rank analysis yields a new result (positive or negative) not implied by Theorems 1--5
- The circumvention landscape provides the definitive "what works / what doesn't" for the thesis
- The results integrate into Chapter 9 naturally


## What NOT to do

- Do NOT re-derive Theorems 1--5. They are correct and verified.
- Do NOT re-derive results from other experiments. Import by citation.
- Do NOT modify files outside `src/experiments/12_circumventing_barrier/`.
- Do NOT attempt all escape routes from Part VII. Focus on higher-rank H_0 only.
- Do NOT write vague discussions of escape routes. Every claim must be precise.
- Do NOT introduce new notation without checking proof.md's existing conventions.
