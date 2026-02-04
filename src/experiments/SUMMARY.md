# Summary

Research threads extending the published work on adiabatic quantum optimization.


## Foundation

The thesis builds on two key papers:

1. **Original paper** (`paper/`): Proves A_1 is NP-hard to approximate, #P-hard to compute exactly. Shows AQO achieves O(2^{n/2}) with the right schedule, but constructing that schedule requires knowing A_1.

2. **Guo-An 2025** (`citations/`): Proves power-law scheduling u'(s) ~ Delta^p achieves O(1/Delta_*) error. Shows p = 3/2 is optimal for linear gaps under the measure condition.


## Active Research Threads

### Completed

| ID | Name | Status | Key Result |
|----|------|--------|------------|
| 02 | robust_schedules | Complete | Hedging over [u_L, u_R] achieves error ratio (u_R - u_L). Constant-factor approximation with bounded uncertainty. Lean formalized. |
| 04 | separation_theorem | Complete | Gap-uninformed fixed schedules require Omega(2^{n/2}) overhead. Lean formalized. |
| 05 | adaptive_schedules | Complete | Adaptive AQO with Theta(n) measurements achieves T = O(T_inf). Circumvents classical hardness. |
| 06 | measure_condition | Complete | T = Theta(1/Delta_*^{3-2/alpha}) where alpha is gap flatness. Dichotomy is FALSE - scaling forms a spectrum. Lean formalized. |
| 07 | partial_information | Complete | T(epsilon) = T_inf * Theta(max(1, epsilon/delta_A1)). Linear interpolation, no thresholds. Lean verified. |


### Exploratory

| ID | Name | Status | Goal |
|----|------|--------|------|
| 08 | structured_tractability_v2 | Proposed | Find problem classes with tractable A_1 |
| 10 | information_theoretic | Proposed | Fundamental limits beyond adiabatic framework |


### Legacy (Archived)

| ID | Name | Status | Notes |
|----|------|--------|-------|
| 01 | precision_gap | Archived | Subsumed by 07 |
| 03 | structured_tractability | Archived | Refined as 08 |

## Priority Ranking

Based on novelty, feasibility, and potential impact:

1. **07_partial_information** (High feasibility, connects existing work)
   - Natural extension of 04
   - Clear mathematical framework
   - Practical implications

2. **08_structured_tractability_v2** (High impact if positive result)
   - Positive result = first provably optimal AQO for NP-hard problems
   - Negative result = stronger impossibility

3. **10_information_theoretic** (Very high novelty, low feasibility)
   - Most ambitious
   - Would establish truly fundamental limits
   - High risk / high reward


## Key Open Questions

1. ~~Can adaptive schedules circumvent the separation theorem?~~ **ANSWERED** (Experiment 05): YES. Adaptive AQO with Theta(n) measurements achieves T = O(T_inf), fully matching informed performance. The classical NP-hardness of computing s* does not prevent quantum adaptive algorithms from achieving optimal performance.

2. ~~What is the interpolation T(epsilon) between informed and uninformed?~~ **ANSWERED** (Experiment 07): T(epsilon) = T_inf * Theta(max(1, epsilon/delta_A1)) where delta_A1 = Theta(2^{-n/2}). The interpolation is LINEAR in epsilon. NP-hard precision (1/poly(n)) gives nearly full exponential overhead.

3. ~~When does the measure condition fail, and what happens then?~~ **ANSWERED** (Experiment 06): Measure condition fails for flat minima (alpha > 1). Scaling is T = Theta(1/Delta_*^{3-2/alpha}), forming a continuum from 1 to 3.

4. ~~Can fixed schedules achieve constant-factor approximation with bounded uncertainty?~~ **ANSWERED** (Experiment 02): Yes. Hedging over [u_L, u_R] achieves error ratio (u_R - u_L). The calibration barrier is "soft" with structural knowledge.

5. Are there NP-hard problems with tractable A_1? (Experiment 08)

6. Is the adiabatic framework uniquely limited compared to circuit model? (Experiment 10)


## Major Contributions

### Experiment 02: Robust Schedules (Hedging Theorem)

**Result**: Hedging schedules achieve error ratio (u_R - u_L) compared to uniform.

**Main Theorem**: When crossing position u* is known to lie in [u_L, u_R]:
```
Error_hedge / Error_unif -> (u_R - u_L)   as I_slow/I_fast -> infinity
```

**Practical implication**: For [0.4, 0.8], hedging achieves 60% error reduction.

**Key insight**: The calibration barrier is "soft" - with partial structural knowledge (bounded uncertainty), the overhead is constant (not exponential).

**Formalization**: Lean 4 verified (no sorry, no axioms). Numerical verification confirms convergence.

**Novelty confirmed**: No prior work on competitive ratio of fixed hedging schedules with bounded uncertainty.


### Experiment 05: Adaptive Schedules

**Result**: Adaptive AQO with O(n) measurements achieves T = O(T_inf).

**Protocol**: Binary search + restart
- Phase 1: Binary search for crossing position using fast evolution + measurement
- Phase 2: Execute with informed schedule using learned crossing location

**Key insight**: COMPUTING s* classically is NP-hard, but DETECTING s* quantumly is easy via Landau-Zener transitions. The quantum system encodes information about the crossing.

**Lower bound**: Omega(n) measurements are necessary (information-theoretic).

**Significance**: Resolves open question from original paper. Classical hardness doesn't imply quantum hardness for this task.


### Experiment 06: Measure Condition (Scaling Spectrum)

**Result**: Runtime T = Theta(1/Delta_*^{3-2/alpha}) where alpha is the gap flatness exponent.

**Main Theorems**:
- Theorem 1 (Geometric Characterization): Measure condition holds iff alpha <= 1
- Theorem 2 (Scaling Spectrum): Exponent gamma = 3 - 2/alpha forms continuum [1, 3)

**Key insight**: The dichotomy conjecture (either O(1/Delta_*) or O(1/Delta_*^2)) is FALSE. Flat-bottomed gap minima create a continuous spectrum of runtimes.

**Summary Table**:
| alpha | gamma | Measure Condition | Runtime |
|-------|-------|-------------------|---------|
| 1     | 1     | Holds             | Theta(1/Delta_*) |
| 1.5   | 5/3   | Fails             | Theta(1/Delta_*^{5/3}) |
| 2     | 2     | Fails             | Theta(1/Delta_*^2) |
| 3     | 7/3   | Fails             | Theta(1/Delta_*^{7/3}) |

**Formalization**: Lean 4 verified (no sorry, only standard axioms: propext, Classical.choice, Quot.sound).

**Novelty**: First proof that measure condition is necessary (not just sufficient) for Guo-An's quadratic speedup.


### Experiment 07: Partial Information (Interpolation Theorem)

**Result**: T(epsilon) = T_inf * Theta(max(1, epsilon/delta_A1)) for A_1 precision epsilon.

**Main Theorem (Interpolation)**: For precision epsilon in A_1:
- When epsilon <= delta_A1: T = Theta(T_inf) (optimal)
- When epsilon > delta_A1: T = Theta(T_inf * epsilon/delta_A1) (linear penalty)

where delta_A1 = Theta(2^{-n/2}) is the required precision.

**Key insights**:
1. Interpolation is LINEAR in epsilon (not sqrt, not threshold)
2. No phase transitions - every bit of precision helps proportionally
3. NP-hard precision (1/poly(n)) gives T = Theta(T_inf * 2^{n/2}/poly(n)) - nearly full exponential overhead

**Formalization**: Lean 4 verified (no sorry, only standard axioms: propext, Classical.choice, Quot.sound).

**Novelty**: First explicit T(epsilon) formula relating runtime to parameter precision. Not in Roland-Cerf 2002, Jansen-Ruskai-Seiler 2007, or Guo-An 2025.
