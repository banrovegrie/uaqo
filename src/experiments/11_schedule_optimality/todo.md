# Experiment 11: Schedule Optimality -- `todo.md`

Purpose: maintain a single consolidated place for open threads, partial results, and
next actions while the experiment is evolving.


## Plans

### A. Schedule selection under partial information (connection to Exps 07 + 10)

**A0. Characterize p=3/2 sensitivity to parameter errors**
- [ ] Derive error propagation for JRS p=3/2 schedule: if the measure condition
      constant \(C\) is estimated with error \(\delta_C\), what is the resulting
      runtime degradation?
- [ ] Derive error propagation for \(g_{\min}\) error: if \(g_{\min}\) is known to
      multiplicative factor \((1 \pm \delta)\), what is the runtime impact?
- [ ] Compare to RC p=2 error propagation (already characterized by Exp 07):
      \(T(\varepsilon) = T_{\mathrm{inf}} \cdot \Theta(\max(1, \varepsilon/\delta_{A_1}))\).

**A1. Write the comparison proposition**
- [ ] State as a proposition: "Under partial \(A_1\) knowledge to precision
      \(\varepsilon\), the RC schedule achieves ... while the JRS schedule achieves ..."
- [ ] Include practical guidance: which schedule degrades more gracefully?
- [ ] Add numerical verification for a concrete instance (e.g. Grover \(N = 256\))
      showing both degradation curves.


### B. Quantitative comparison for structured families (connection to Exp 08)

**B0. Compute C and I for a structured instance**
- [ ] Read Exp 08 Prop 13 (ferromagnetic Ising bridge): extract spectral parameters
      \((A_1, A_2, \Delta, s_0)\) for a concrete small instance.
- [ ] Evaluate \(C\) (Theorem A formula) and \(I\) (integral constant) for this instance.
- [ ] Compute \(C^2/I\) and compare to Grover ratio \(\approx 0.603\).

**B1. State as a remark**
- [ ] Add computational remark in proof.md after Extension E.
- [ ] Add verification to `lib/verify_extensions.py`.


### C. Chapter 9 integration

**C0. Determine placement**
- [ ] Read Chapter 9 outline in `README.md` (around line 685, "Measure Condition
      and Scaling" section sourcing Exp 06). Exp 11 extends Exp 06.
- [ ] Natural placement: subsection within or immediately after the Measure Condition
      section, titled "Schedule Selection" or "Which Schedule to Use".

**C1. Write insertion outline**
- [ ] Map proof.md results to Chapter 9 content:
      - Theorems A--C: measure condition + runtime recovery (one subsection)
      - Extensions E--F: constant comparison + classification by alpha (one subsection)
      - Extension G: structural alpha=1 (one remark)
      - Gap A result: partial-information comparison (one subsection)
- [ ] Note which open questions carry into the Conclusion.


### D. Open question investigation (optional, low priority)

- [ ] Explicit JRS constant computation for the paper's Hamiltonian.
- [ ] Non-power-law schedule comparison (e.g. exponential slowdown near \(s^*\)).


### E. Paper-grade checklist

- [x] Core connection established (Theorems A--C).
- [x] Grover specialization with exact constants (Theorems B, D).
- [x] Framework comparison across gap geometries (Extensions E--H).
- [x] Lean verification of algebraic core.
- [x] Numerical verification (5 claims).
- [x] Novelty positioning paragraph.
- [ ] Partial-information schedule comparison (novel contribution).
- [ ] Structured-family quantitative comparison.
- [ ] Chapter 9 insertion outline.


## Progress

- 2026-02-06: Parts I--VIII of `proof.md` complete. Theorems A--H + Extensions
  proved. 2 Lean axioms, rest axiom-free. 5 numerical claims verified. All 4
  conjectures resolved. Created `todo.md`.


## Findings

### Solid (already correct)

- The paper's gap profile satisfies Guo-An's measure condition with explicit
  constant \(C \leq 3A_2/(A_1(A_1+1)) + 30(1-s_0)/\Delta\).
- Grover case: \(C = 1\) exactly (Lean-verified).
- Both p=2 (RC) and p=3/2 (JRS) recover \(T = O(\sqrt{NA_2/d_0}/\varepsilon)\).
- The paper's Hamiltonian always has gap flatness \(\alpha = 1\) (boundary case).
- At \(\alpha = 1\): JRS constant \(C^2\) is smaller than RC integral \(I\) by
  factor \(\sim c_L\); for Grover, \(C^2/I \to 0.603\) as \(N \to \infty\).

### Missing (needed for novelty)

- A schedule comparison under partial information connecting to Exp 07.
- Quantitative comparison for structured families connecting to Exp 08.
- Chapter 9 insertion outline.

### Chapter 9 insertion outline (draft)

- **Placement:** subsection within or after "Measure Condition and Scaling" (Exp 06).
- **Content:** (1) measure condition holds for the paper's gap with explicit \(C\);
  (2) both RC and JRS recover optimal runtime; (3) framework comparison: which is
  tighter depends on \(c_L\); (4) practical guidance under partial information.
- **Deferred:** explicit JRS constant, non-power-law schedules (to Conclusion/future).
