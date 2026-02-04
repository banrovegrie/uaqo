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
| 04 | separation_theorem | Complete | Gap-uninformed fixed schedules require Omega(2^{n/2}) overhead. Lean formalized. |


### In Progress

| ID | Name | Status | Goal |
|----|------|--------|------|
| 07 | partial_information | Proposed | Characterize T(epsilon) for precision epsilon in A_1 |
| 05 | adaptive_schedules | Proposed | Fundamental limits of adaptive probing |
| 06 | measure_condition | Proposed | When does Guo-An's quadratic improvement fail? |


### Exploratory

| ID | Name | Status | Goal |
|----|------|--------|------|
| 08 | structured_tractability_v2 | Proposed | Find problem classes with tractable A_1 |
| 09 | guo_an_gap | Proposed | Prove Guo-An schedule construction is NP-hard |
| 10 | information_theoretic | Proposed | Fundamental limits beyond adiabatic framework |


### Legacy (Archived)

| ID | Name | Status | Notes |
|----|------|--------|-------|
| 01 | precision_gap | Archived | Subsumed by 07 |
| 02 | robust_schedules | Archived | Numerical experiments, see archive/ |
| 03 | structured_tractability | Archived | Refined as 08 |


## Priority Ranking

Based on novelty, feasibility, and potential impact:

1. **07_partial_information** (High feasibility, connects existing work)
   - Natural extension of 04
   - Clear mathematical framework
   - Practical implications

2. **05_adaptive_schedules** (High novelty, medium feasibility)
   - No existing work on adaptive limits
   - Could be a standalone paper
   - Information-theoretic approach

3. **06_measure_condition** (High feasibility, medium novelty)
   - Direct extension of Guo-An
   - Concrete calculations possible
   - Fills gap in literature

4. **08_structured_tractability_v2** (High impact if positive result)
   - Positive result = first provably optimal AQO for NP-hard problems
   - Negative result = stronger impossibility

5. **09_guo_an_gap** (Medium novelty, high feasibility)
   - Mostly bookkeeping to unify hardness results
   - Important for completeness

6. **10_information_theoretic** (Very high novelty, low feasibility)
   - Most ambitious
   - Would establish truly fundamental limits
   - High risk / high reward


## Key Open Questions

1. Can adaptive schedules circumvent the separation theorem?
2. What is the interpolation T(epsilon) between informed and uninformed?
3. When does the measure condition fail, and what happens then?
4. Are there NP-hard problems with tractable A_1?
5. Is the adiabatic framework uniquely limited compared to circuit model?
