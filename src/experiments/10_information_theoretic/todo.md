# Experiment 10: Information-Theoretic Limits -- `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Cross-experiment synthesis (unified model comparison)

**A0. Read and import neighboring results**
- [ ] Read Exp 12 `main.md` and `proof.md`: extract the no-go theorem statement
      (Theorem 5: within rank-one instance-independent design, the \(A_1\) barrier is
      unbreakable). Record exact statement + assumptions.
- [ ] Read Exp 13 `main.md` and `proof.md`: extract quantum-classical separation for
      \(A_1\) estimation at precision \(2^{-n/2}\) (quantum \(O(2^{n/2})\), classical
      \(\Omega(2^n)\)). Record exact theorem numbers.
- [ ] Read Exp 08 `main.md` and `proof.md`: extract structured tractability results
      (Prop 8: bounded treewidth exact \(A_1\); Props 13--14: ferromagnetic Ising
      approximate \(A_1\); schedule-precision scale). Record which families make the
      \(A_1\) barrier dissolve.

**A1. Write the Complete Model Comparison Theorem (Part X of proof.md)**
- [ ] Draft a unified theorem statement covering all computational models for
      ground-state finding of \(n\)-qubit diagonal Hamiltonians with \(d_0\) ground
      states. Each row of the table must cite its source precisely.
- [ ] Include rows for: circuit (Durr-Hoyer), adiabatic gap-informed, adiabatic
      \(C\)-bit partial, adiabatic uninformed, adiabatic adaptive, adiabatic with
      modified Hamiltonian (Exp 12 no-go), quantum \(A_1\) estimation, classical \(A_1\)
      estimation.
- [ ] Add a remark on structured families: when \(A_1\) is tractable (Exp 08), the
      "NP-hard precomputation" row drops to polynomial, qualitatively changing the
      landscape.
- [ ] State the scope limitation explicitly: results apply to ground-state finding of
      diagonal Hamiltonians; other tasks (energy estimation, full spectrum
      reconstruction) may require spectral information even in the circuit model.
- [ ] Add numerical verification to `lib/verify.py` (e.g. sanity-check that quantum
      estimation cost matches adiabatic runtime for concrete \(N, d_0\) values).


### B. Precision-aware model comparison (connection to Exp 13)

**B0. State the quantum pre-computation tradeoff**
- [ ] Proposition: quantum \(A_1\) estimation at precision \(2^{-n/2}\) costs
      \(O(2^{n/2} \cdot \mathrm{poly}(n))\) (Exp 13, Theorem 2). Optimal adiabatic
      runtime is \(T_{\mathrm{inf}} = \Theta(\sqrt{N/d_0})\). Total: quantum estimation
      + informed adiabatic = \(O(\sqrt{N/d_0} \cdot \mathrm{poly}(n))\), matching
      Durr-Hoyer up to polylog factors.
- [ ] Contrast: classical estimation costs \(\Omega(2^n)\) (Exp 13, Theorem 3), so
      classical precomputation + adiabatic = \(\Omega(N)\), worse than brute force.
- [ ] State the structural insight: the quantum-classical gap in \(A_1\) estimation
      equals the computational gap between circuit and adiabatic models. Both stem from
      amplitude amplification giving \(\sqrt{N}\) scaling.
- [ ] Add numerical sanity check: for \(N = 256\), \(d_0 = 1\), verify quantum
      estimation cost \(\approx 16\) matches \(T_{\mathrm{inf}} = 16\).


### C. Conjecture 5: continuous-time \(A_1\) barrier (high risk / high reward)

**C0. Scope the attempt**
- [ ] Re-read Part IX of `proof.md` and the Farhi et al. (2008) evidence carefully.
      Identify the precise point where their argument requires specific spectral
      structure that a general continuous-time rank-one algorithm lacks.
- [ ] Decide: attempt monotone-controls restricted version, weaker
      information-dependence version, or documented obstruction.

**C1. Monotone controls (target (a), highest value)**
- [ ] Define the restricted class precisely: continuous-time rank-one algorithms with
      \(f(t)\) non-increasing, \(g(t)\) non-decreasing, \(f(0) > 0\), \(g(0) = 0\),
      \(g(T) > 0\).
- [ ] Attempt proof: show that monotone controls must traverse the avoided crossing
      and cannot tune speed without knowing \(s^*\).
- [ ] If successful: write as a proposition in proof.md with full proof.

**C2. Weaker version (target (b))**
- [ ] Attempt: prove that any rank-one algorithm achieving
      \(T = O(\sqrt{N/d_0})\) must have controls that depend on \(A_1\)
      (or on \(\Omega(n/2)\) bits of spectral information).
- [ ] If successful: write as a proposition connecting to Part IV's communication
      framework.

**C3. Documented obstruction (target (c), fallback)**
- [ ] If (a) and (b) fail: write a precise "Remark: Difficulty of Conjecture 5"
      section in proof.md.
- [ ] State what was tried, where it breaks, and what technique would be needed.
- [ ] Identify the specific barrier to extending Farhi et al.'s Theorem 1 beyond
      their spectral structure.


### D. Chapter 9 integration

**D0. Determine placement**
- [ ] Read the Chapter 9 outline in the main `README.md` (around line 621).
      Current sections: Separation Theorem (Exp 04), Partial Information (Exp 07),
      Robust Schedules (Exp 02), Adaptive Schedules (Exp 05), Measure Condition
      (Exp 06), Ignorance Taxonomy (synthesis), Central Claim.
- [ ] Exp 10 fits as the **capstone section** after the Ignorance Taxonomy:
      "Having characterized how information determines runtime within the adiabatic
      model, we ask whether this barrier is fundamental. Answer: no."

**D1. Write insertion outline**
- [ ] Map proof.md theorems to Chapter 9 propositions:
      - Theorems 1--2 (query bounds + Durr-Hoyer): one proposition
      - Theorem 3 + Props 6--8 (model separation + \(A_1\)-blindness): one theorem
      - Theorem 7 (bit-runtime tradeoff): one corollary
      - Synthesis theorem (A1 above): capstone theorem
      - Precision corollary (B0 above): closing remark
- [ ] Specify how the model comparison table integrates with the Ignorance Taxonomy.
- [ ] Note which open questions carry into the Conclusion (Conjecture 5, classical
      communication complexity, spectral info for other tasks).


### E. Paper-grade checklist (what "done" looks like)

- [x] Core model-separation theorem (Theorems 1--5).
- [x] \(A_1\)-blindness formalization (Propositions 6--8).
- [x] Unified bit-runtime landscape (Theorems 6--7).
- [x] Lean verification of algebraic core (14 theorems).
- [x] Numerical verification (5 test suites, all pass).
- [x] Novelty positioning paragraph.
- [ ] Cross-experiment synthesis theorem.
- [ ] Precision-aware model comparison (connection to Exp 13).
- [ ] Conjecture 5 progress OR documented obstruction.
- [ ] Chapter 9 insertion outline.


## Progress

- 2026-02-06: Parts I--IX of `proof.md` complete. 14 Lean theorems verified.
  5 numerical test suites pass. Conjectures 1--4 resolved. Conjecture 5 stated
  with evidence, remains open. Created `todo.md`.


## Findings

### Solid (already correct)

- The Grover lower bound \(\Omega(\sqrt{N/d_0})\) is the only universal query
  complexity lower bound for ground-state finding.
- The \(A_1\) barrier is model-specific: circuit algorithms (Durr-Hoyer) bypass it
  entirely with zero mutual information about \(A_1\).
- Communication complexity: \(C_{\mathrm{circuit}} = 0\),
  \(C_{\mathrm{adiabatic}} = \Theta(n)\), \(C_{\mathrm{adaptive}} = 0\).
- Bit-runtime tradeoff: \(T(C) = T_{\mathrm{inf}} \cdot 2^{n/2 - C}\) within the
  adiabatic model; each additional bit of \(A_1\) halves runtime.
- \(A_1\)-blindness: conditioned on success,
  \(I(X_{\mathrm{DH}}; A_1 \mid S_0, E_0) = 0\) (exactly zero).

### Missing (needed for novelty)

- A unified synthesis theorem integrating results from Exps 08, 10, 12, 13 into
  a single complete model comparison.
- A precision-aware corollary connecting the bit-runtime tradeoff (Theorem 7) to
  the quantum-classical \(A_1\) estimation gap (Exp 13).
- Progress on Conjecture 5 (continuous-time \(A_1\) barrier), even if only a
  restricted-class proof or documented obstruction.
- Chapter 9 insertion outline specifying how Exp 10 integrates as the capstone
  section.

### Chapter 9 insertion outline (draft)

- **Motivation:** the Ignorance Taxonomy (Exps 02, 04, 05, 06, 07) characterizes
  how information determines runtime *within* the adiabatic model. Is this barrier
  fundamental?
- **Core negative result:** Durr-Hoyer achieves optimal \(\Theta(\sqrt{N/d_0})\)
  without any spectral information (Theorem 2). The \(A_1\) barrier is an artifact
  of the adiabatic path, not a property of the computational task.
- **\(A_1\)-blindness:** circuit-model output is independent of \(A_1\) conditioned
  on success (Props 6--8). Adiabatic output depends on \(A_1\) through the crossing
  position \(s^*\).
- **Complete landscape:** unified model comparison (synthesis theorem from A1 above)
  covering circuit, adiabatic, adaptive, modified-Hamiltonian, and estimation models.
- **Precision bridge:** quantum \(A_1\) estimation matches adiabatic runtime in
  cost, so "estimate then evolve" matches Durr-Hoyer; classical estimation does not.
- **Scope:** Conjecture 5 (continuous-time barrier) and open questions on classical
  communication complexity and spectral information for other tasks.
