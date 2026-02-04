# Adaptive Schedules: Fundamental Limits of Adaptive Probing

## Problem Statement

The gap-uninformed separation theorem (experiment 04) proves that any *fixed* schedule not knowing the gap position requires Omega(2^{n/2}) more time than informed schedules. But this leaves open the question: what about *adaptive* schedules that can probe the system during evolution?

An adaptive schedule can:
- Measure the current state (fidelity, energy, etc.)
- Adjust the schedule based on measurements
- Potentially learn about the gap position during evolution

**Central Question**: Can an adaptive schedule with poly(n) measurements approach the informed runtime, or do fundamental barriers remain?


## Why Novel

Existing work on adaptive/gap-uninformed schedules:
- Han-Park-Choi 2025: Constant speed schedule with adaptive stopping, but no fundamental limits
- Shingu-Hatomura 2025: Geometric method for schedule adaptation, but no complexity analysis
- Matsuura et al. 2021: Variational approach, no separation bounds
- Our experiment 04: Only addresses fixed schedules

**Gap**: No one has proven what adaptive schedules *cannot* do. This is the natural next question after 04.


## Conjectures

### Conjecture 1 (Weak Lower Bound)
Any adaptive schedule making k measurements during evolution requires time at least:
```
T_adaptive >= T_informed * f(k, n)
```
where f(k, n) -> infinity as k -> 0 and f(k, n) -> 1 as k -> infinity.

### Conjecture 2 (Strong Lower Bound)
Any adaptive schedule making poly(n) measurements still requires:
```
T_adaptive >= T_informed * Omega(poly(n))
```
That is, polynomial measurements cannot achieve the exponential speedup.

### Conjecture 3 (Upper Bound - Positive)
There exists an adaptive schedule making O(n) measurements that achieves:
```
T_adaptive <= T_informed * O(poly(n))
```
This would show adaptive schedules partially circumvent the hardness.


## Approach

### Strategy 1: Information-Theoretic Lower Bound
Model the problem as parameter estimation:
- The unknown parameter is s* = A_1/(A_1+1), the crossing position
- Each measurement provides some information about s*
- Use Fisher information or Cramer-Rao bounds to limit precision

Key insight: A single measurement at time t gives information I(t) about s*. Total information from k measurements is bounded. If precision epsilon requires information I > I_0(epsilon), then k >= I_0(epsilon)/max_t I(t).

### Strategy 2: Adversarial Argument Extension
Extend the 04 separation argument:
- After each measurement, the adversary updates the gap class
- The gap can still be placed adversarially subject to consistency
- Show that measurements don't collapse uncertainty fast enough

### Strategy 3: Quantum Query Complexity
Frame as oracle problem:
- Oracle encodes the gap function Delta(s)
- Query complexity of finding the minimum to precision epsilon
- Lower bounds from quantum query complexity (polynomial method, adversary method)


## Technical Framework

### Model of Adaptive Schedule
An adaptive schedule is a sequence (s_1, t_1), (s_2, t_2), ..., (s_k, t_k) where:
- s_i: [0, T] -> [0, 1] is the schedule in round i
- t_i in [0, T] is the measurement time
- s_{i+1} depends on measurement outcomes M_1, ..., M_i

### Measurement Model
After evolving for time t under schedule s:
- State: |psi(t)> = U_s(t)|psi_0>
- Measurement M: some POVM, returns classical outcome m
- Information: mutual information I(s*; m)

### The Game
1. Nature (adversary) chooses gap function Delta in class G[s_L, s_R, Delta_*]
2. Algorithm chooses adaptive strategy
3. Goal: achieve fidelity >= 1 - epsilon with ground state
4. Cost: total evolution time T

**Theorem Goal**: For any adaptive strategy with k measurements, there exists Delta in G such that T >= T_lower(k).


## Results

**Status**: CONJECTURAL

No proofs yet. Need to:
1. Formalize the measurement model precisely
2. Derive Fisher information for gap estimation from fidelity measurements
3. Connect to query complexity literature


## Open Questions

1. What measurements are most informative? (Energy? Fidelity? Gap directly via QPE?)
2. Does the measurement disturb the evolution significantly?
3. Is there a separation between coherent and incoherent strategies?
4. Can we prove a quantum query lower bound for gap-minimum finding?


## Connection to Other Experiments

- Builds on 04 (separation theorem for fixed schedules)
- Related to 07 (partial information) - what if measurements give partial info?
- Could inform 09 (Guo-An gap) - adaptive learning of Delta(s)


## References

1. Han-Park-Choi 2025 - Constant speed adaptive AQO
2. Shingu-Hatomura 2025 - Geometrical method for AQO
3. Matsuura et al. 2021 - Variational adiabatic gauge transformation
4. Ambainis 2002 - Quantum query complexity lower bounds
5. Quantum Fisher information literature


## Status

**Phase**: Proposed

Next steps:
1. Literature survey on quantum parameter estimation
2. Formalize the information-theoretic framework
3. Compute Fisher information for simple measurement models
4. Attempt adversarial argument extension
