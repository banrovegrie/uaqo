# TODO: Research Threads

Active tasks across all experiments.


## Immediate Priority: 08_structured_tractability_v2

Looking for positive results.

### Tasks

- [ ] Complete analysis of unique solution case
- [ ] Investigate planted solution construction
- [ ] Survey specific NP-hard problems for special structure
- [ ] Attempt impossibility proof (no sweet spot)


## Long-term: 10_information_theoretic

The most ambitious direction.

### Tasks

- [ ] Formalize oracle model
- [ ] Review query complexity techniques
- [ ] Prove basic Grover lower bound in this framework
- [ ] Define "additional information" formally


## Completed

### 07_partial_information (NEW)

- [x] Derive precision-runtime tradeoff formula: T(epsilon) = T_inf * max(1, epsilon/delta_A1)
- [x] Prove precision propagation lemma (A_1 error to s* error)
- [x] Prove lower bound from separation theorem
- [x] Prove trivial lower bound (T >= T_inf always)
- [x] Prove interpolation theorem combining both bounds
- [x] Explicit formula for unstructured search
- [x] Lean formalization (no sorry, standard axioms only)
- [x] Novelty confirmed: not in Roland-Cerf, JRS, or Guo-An
- [ ] Numerical verification for n = 8, 10, 12 (optional)

### 05_adaptive_schedules

- [x] Literature survey confirming novelty
- [x] Formalize the measurement model (fast evolution + H_z measurement)
- [x] Prove upper bound: O(n) measurements achieve T = O(T_inf)
- [x] Prove lower bound: Omega(n) measurements necessary
- [x] Explicit protocol: binary search + restart
- [x] Resolve open question from original paper
- [ ] Numerical validation (optional)
- [ ] Compare with Han-Park-Choi 2025 (optional)

### 04_separation_theorem

- [x] Formalize gap class G[s_L, s_R, Delta_*]
- [x] Prove adversarial lower bound
- [x] Prove uniform slow schedule achieves bound
- [x] Apply to unstructured search: Omega(2^{n/2}) separation
- [x] Verify novelty (7 papers checked)
- [x] Lean formalization
- [ ] Make constants explicit (optional refinement)

### 06_measure_condition

- [x] Construct examples violating measure condition (flat minima)
- [x] Prove scaling T = Theta(1/Delta_*^{3-2/alpha}) for alpha-flat gaps
- [x] Establish dichotomy is FALSE: scaling forms continuum
- [x] Lean formalization (no sorry, standard axioms only)
- [ ] Numerical verification (optional)

### 02_robust_schedules

- [x] Hedging schedule analysis
- [x] Bounded uncertainty framework
- [x] Error ratio (u_R - u_L) achieved
- [x] Write formal proof.md
- [x] Lean formalization (no sorry, no axioms)
- [x] Numerical verification (lib/verify_hedging_theorem.py, lib/direct_simulation_test.py)
- [x] Novelty confirmed via literature search


## Notes

- 02 complete with Lean formalization - novel result on hedging schedules
- 04 complete with Lean formalization - gap-uninformed separation theorem
- 05 complete - major result answering open question from original paper
- 06 complete with Lean formalization - scaling spectrum refutes dichotomy conjecture
- 07 complete with Lean formalization - interpolation theorem, novel contribution
- 08 is now top priority - high-risk: might prove impossibility instead of finding examples
- 10 should wait until other threads mature
- Consider writing up 02, 05, 06, and 07 as standalone contributions
- Five experiments now complete with formal verification (02, 04, 05, 06, 07)
