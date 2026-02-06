# Experiment 12: Circumventing the Barrier -- `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Higher-rank initial Hamiltonians (primary escape route investigation)

**A0. Derive the generalized secular equation**
- [ ] For \(H_0 = -P\) with \(P\) a rank-\(k\) projector, write the eigenvalue
      equation for \(H(s) = -(1-s)P + sH_z\). The secular equation becomes a
      \(k\)-dimensional problem.
- [ ] Specialize to \(k = 2\): \(P = |\psi_0\rangle\langle\psi_0| +
      |\phi\rangle\langle\phi|\). Derive the \(2 \times 2\) effective Hamiltonian
      in the \(\{|\psi_0\rangle, |\phi\rangle\}\) subspace.

**A1. Analyze crossing dependence on \(A_1\)**
- [ ] For \(k = 2\): does the crossing position \(s^*\) depend on \(A_1\) alone,
      or also on the overlaps \(\langle\phi|x\rangle\)? Can \(|\phi\rangle\) be
      chosen to eliminate \(A_1\) dependence?
- [ ] If crossing still depends on \(A_1\): prove this as a proposition extending
      Theorem 5 to rank-2. Add numerical verification.
- [ ] If crossing can be made \(A_1\)-independent: prove the positive result.
      Determine minimum rank needed. Check if the resulting schedule achieves
      \(O(\sqrt{N/d_0})\) runtime.

**A2. Document outcome**
- [ ] If analysis is inconclusive: document the obstruction precisely. State
      what makes higher-rank harder (loss of the permutation argument from Theorem 2,
      additional degrees of freedom in overlaps).
- [ ] Add numerical experiments to `lib/ancilla_spectrum.py` for rank-2 systems.


### B. Lean formalization

**B0. Core structure**
- [ ] Create `lean/CircumventingBarrier.lean` with spectral parameter definitions,
      crossing position, and weights \(w_k = d_k/N\).
- [ ] Create `lean/CircumventingBarrier/Basic.lean` with Theorem 2 (Universality)
      statement and proof (permutation argument).
- [ ] Create `lean/CircumventingBarrier/NoGo.lean` with Theorem 5 (No-Go) statement.
      Axiomatize Theorems 1, 3, 4 as component axioms; prove Theorem 5 as composition.

**B1. Verification**
- [ ] Ensure `lake build` succeeds with 0 errors, 0 sorries.
- [ ] Follow conventions from `src/lean/` (Mathlib imports, naming, documentation).


### C. Cross-experiment synthesis (circumvention landscape)

**C0. Import results**
- [ ] Read and cite: Exp 05 Theorem 1 (adaptive circumvention), Exp 10 Theorem 2
      (circuit bypass), Exp 13 Theorem 2 (quantum estimation), Exp 08 Props 8--13
      (structured tractability).
- [ ] Verify each cited result's exact statement and assumptions.

**C1. Write the circumvention landscape**
- [ ] State as a Proposition or structured Remark in proof.md (after Part VII).
- [ ] "CAN circumvent" list: circuit model, adaptive measurement, quantum estimation,
      structured tractability.
- [ ] "CANNOT circumvent" list: product ancilla, non-uniform states, fixed coupling,
      multi-segment paths, any rank-one instance-independent modification.
- [ ] Scope note: rank-one and instance-independence are the binding constraints.


### D. Chapter 9 integration

**D0. Determine placement**
- [ ] Read Chapter 9 outline in `README.md`. Natural placement: after Adaptive
      Schedules (Exp 05), as "Can Hamiltonian modifications achieve the same?
      Answer: no."
- [ ] Alternative: part of the capstone synthesis section with Exp 10.

**D1. Write insertion outline**
- [ ] Map proof.md theorems to Chapter 9 content:
      - Theorems 1--2: invariance + universality (key insight subsection)
      - Theorem 5: no-go (main result)
      - Part VII: escape routes (discussion subsection)
      - Gap C result: circumvention landscape (synthesis)
- [ ] Note which open questions carry into the Conclusion.


### E. Paper-grade checklist

- [x] No-go theorem proved (Theorem 5).
- [x] Universality of uniform superposition (Theorem 2, key insight).
- [x] All 5 component theorems with complete proofs.
- [x] Escape routes analysis (Part VII).
- [x] Numerical verification (822-line Python script).
- [x] Novelty positioning paragraph.
- [ ] Higher-rank investigation (positive, negative, or documented obstruction).
- [ ] Lean formalization (at least core structure).
- [ ] Circumvention landscape (cross-experiment synthesis).
- [ ] Chapter 9 insertion outline.


## Progress

- 2026-02-06: Parts I--VII of `proof.md` complete. Theorems 1--5 proved.
  Corollary on non-adiabatic oscillation proved. 6 open questions documented.
  Numerical verification passes. Created `todo.md`.


## Findings

### Solid (already correct)

- Product ancilla extensions leave the crossing at \(s^* = A_1/(A_1+1)\) exactly
  (Theorem 1).
- The uniform superposition is the unique state giving spectrum-independent weights
  (Theorem 2). This is the key insight: instance-independence forces uniform overlaps.
- Fixed couplings, multi-segment paths, and any rank-one instance-independent
  modification cannot eliminate \(A_1\) dependence (Theorems 3--5).
- Non-adiabatic oscillation faces the same crossing structure (Corollary).
- Five specific escape routes identified (Part VII): higher-rank \(H_0\),
  time-dependent couplings, non-instance-independent design, adaptive measurement,
  non-adiabatic protocols.

### Missing (needed for novelty)

- Concrete investigation of higher-rank \(H_0\) (the most promising escape route).
- Cross-experiment synthesis: unified "what works / what doesn't" landscape.
- Lean formalization.
- Chapter 9 insertion outline.

### Chapter 9 insertion outline (draft)

- **Placement:** after Adaptive Schedules (Exp 05) in Chapter 9.
- **Narrative:** "Adaptive measurement circumvents the barrier by acquiring spectral
  information during evolution. Can we instead modify the Hamiltonian to avoid the
  barrier entirely? No — within rank-one instance-independent design."
- **Content:** (1) universality of uniform superposition (Theorem 2); (2) no-go
  theorem (Theorem 5); (3) escape routes analysis; (4) circumvention landscape.
- **Deferred:** higher-rank investigation (to Conclusion/future work if unresolved).
