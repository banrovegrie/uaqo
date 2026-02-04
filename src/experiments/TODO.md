# TODO: Research Threads

Active tasks across all experiments.


## Immediate Priority: 07_partial_information

The interpolation theorem is the most tractable next step.

### Tasks

- [ ] Derive precision-runtime tradeoff formula from JRS bounds
- [ ] Verify formula numerically for n = 8, 10, 12
- [ ] Check for phase transitions at special precision levels
- [ ] Write up theorem statement and proof sketch
- [ ] Consider Lean formalization


## High Priority: 05_adaptive_schedules

The natural follow-up to the separation theorem.

### Tasks

- [ ] Literature survey on quantum parameter estimation
- [ ] Formalize the measurement model precisely
- [ ] Compute Fisher information for fidelity measurements
- [ ] Attempt adversarial argument extension from 04
- [ ] Investigate query complexity connection


## Medium Priority: 06_measure_condition

Direct extension of Guo-An.

### Tasks

- [ ] Construct explicit examples violating measure condition
- [ ] Numerically verify O(1/Delta_*^2) scaling for these examples
- [ ] Attempt lower bound proof via JRS integral analysis
- [ ] Survey which problem classes satisfy/violate condition


## Medium Priority: 09_guo_an_gap

Unifying the hardness results.

### Tasks

- [ ] Formalize reduction: schedule -> A_1
- [ ] Check if Delta_* alone suffices (not full Delta(s))
- [ ] Verify Guo-An's specific examples (Grover, QLSP) have tractable schedules
- [ ] Write up the circularity argument


## Exploratory: 08_structured_tractability_v2

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

### 04_separation_theorem

- [x] Formalize gap class G[s_L, s_R, Delta_*]
- [x] Prove adversarial lower bound
- [x] Prove uniform slow schedule achieves bound
- [x] Apply to unstructured search: Omega(2^{n/2}) separation
- [x] Verify novelty (7 papers checked)
- [x] Lean formalization
- [ ] Make constants explicit (optional refinement)


## Notes

- Start with 07 as warmup before tackling 05
- 06 and 09 can proceed in parallel
- 08 is high-risk: might prove impossibility instead of finding examples
- 10 should wait until other threads mature
