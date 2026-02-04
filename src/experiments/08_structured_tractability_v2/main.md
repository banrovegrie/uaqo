# Structured Tractability: When is A_1 Easy?

## Problem Statement

The original paper proves A_1 is NP-hard to approximate for general Hamiltonians. But it explicitly leaves open the question: are there interesting problem classes where A_1 can be computed efficiently?

**Central Question**: Characterize the boundary between hard and easy A_1 computation. Find problem classes that are:
1. Computationally interesting (classically hard to solve)
2. Have efficiently computable A_1
3. Therefore achieve provably optimal AQO


## Why Novel

The paper proves hardness for general Hamiltonians but says:
> "We leave open the question of whether this limitation may be overcome... by a suitable modification of the adiabatic Hamiltonian... so that the position of the avoided crossing does not depend on the spectrum of the problem Hamiltonian."

This is the most direct path to a positive result: find problems where the hardness barrier doesn't apply.


## Conjectures

### Conjecture 1 (Unique Solution Tractability)
For problems with unique solution (d_0 = 1) and spectral gap Delta >= 1/poly(n):
```
A_1 = 1/Delta + O(1)
```
which is efficiently computable.

### Conjecture 2 (Bounded Degeneracy)
If all degeneracies d_k <= poly(n) and the number of distinct energy levels M <= poly(n), then A_1 is computable in poly(n) time.

### Conjecture 3 (Structure-Hardness Tradeoff)
A_1 is efficiently computable if and only if the problem is classically easy (in P). That is, there's no "sweet spot" of hard problem + easy A_1.


## Candidate Problem Classes

### Class A: Unique Solution Problems
Problems guaranteed to have exactly one satisfying assignment:
- Planted solution instances with unique planting
- Linear systems over finite fields (if solution exists, it's unique)
- Graph problems with uniqueness guarantees

**Analysis**: When d_0 = 1:
```
A_1 = (1/N) * [1/(E_1-E_0) + sum_{k>1} d_k/(E_k-E_0)]
    = (1/N) * [1/Delta + sum_{k>1} d_k/(E_k-E_0)]
```
The first term dominates if Delta is small. If Delta >= 1/poly(n), then A_1 ~ 1/Delta.

### Class B: Structured Energy Landscapes
Problems where the spectrum has special structure:
- Arithmetic progressions: E_k = k * delta
- Geometric structure: E_k = E_0 * r^k
- Low-rank perturbations of known Hamiltonians

**Analysis**: For arithmetic progressions E_k = k/M (normalized):
```
A_1 = (1/N) * sum_{k=1}^{M-1} d_k * M / k
```
This might simplify for specific degeneracy patterns.

### Class C: Planted Solution Instances
Instances constructed with a known planted solution:
- The solver doesn't know the solution
- But the constructor can compute A_1 when building the instance

**Analysis**: If we plant a solution z* and construct H_z such that:
- E_0 = 0 achieved only at z*
- E_k for k > 0 are chosen to make A_1 simple
Then A_1 is known by construction, while finding z* is still hard.

### Class D: Promise Problems
Problems with a promise on the spectrum:
- Promise: either d_0 >= N/2 or d_0 = 1
- The spectrum structure is constrained by the promise

**Analysis**: Promises might enable efficient A_1 computation while preserving computational hardness of the decision problem.


## Approach

### Strategy 1: Analyze Specific Classes
For each candidate class:
1. Derive formula for A_1 in terms of problem parameters
2. Check if formula is efficiently computable
3. Verify the problem remains classically hard

### Strategy 2: Prove Impossibility
Show that for any class with efficient A_1:
- The class is classically solvable, OR
- The class is measure-zero (uninteresting)

This would establish Conjecture 3.

### Strategy 3: Construct Examples
Explicitly construct problem families:
- Start with an NP-hard problem
- Design the Hamiltonian encoding such that A_1 has a closed form
- Verify the encoding preserves hardness


## Technical Details

### A_1 Formula Analysis
```
A_1 = (1/N) * sum_{k=1}^{M-1} d_k / (E_k - E_0)
```

For A_1 to be efficient to compute, we need:
1. M = poly(n) distinct energy levels, AND
2. Each d_k computable in poly(n) time, AND
3. Each E_k known in poly(n) time

The bottleneck is usually computing d_k (counting solutions at energy E_k).

### Connection to Counting Complexity
Computing d_0 exactly is #P-hard (this is #SAT for SAT encodings). But:
- Approximating d_0 might be easier
- Knowing d_0 up to constant factor might suffice for A_1
- For some problem structures, d_k might have closed forms

### Unique Solution Case Deep Dive
When d_0 = 1:
```
A_1 = (1/N) * [1/Delta + sum_{k>1} d_k/(E_k-E_0)]
```
The sum has N-1 terms but groups into M-1 distinct energy levels. If Delta = Theta(1/poly(n)) dominates:
```
A_1 = poly(n)/N + O(1/N) = O(poly(n)/N)
```
Since N = 2^n, this gives A_1 = O(poly(n) * 2^{-n}), which might be computable.

But wait: to know Delta dominates, we need to bound the sum, which requires bounding sum d_k/(E_k-E_0). This still involves the d_k...


## Results

**Status**: EXPLORATORY

The unique solution case seems promising but the analysis is incomplete. The key obstruction is that even if d_0 = 1, we still need information about the d_k for k > 0.


## Open Questions

1. Is there a problem class where A_1 simplifies without needing all d_k?
2. Can approximate knowledge of d_k (to constant factor) suffice?
3. Are there physical Hamiltonians (not NP-hard encodings) with tractable A_1?
4. Does the planted solution construction work?


## Connection to Other Experiments

- This is a refinement of the original 03_structured_tractability
- Positive result would inform 07 (partial information not needed if A_1 exact)
- Negative result (Conjecture 3) would strengthen the hardness barrier narrative


## References

1. Original paper - Section on hardness, discussion of open problems
2. Valiant 1979 - #P-hardness
3. Planted solution literature
4. Promise problem complexity


## Status

**Phase**: Exploratory

Next steps:
1. Complete analysis of unique solution case
2. Investigate planted solution construction
3. Survey specific NP-hard problems for special structure
4. Attempt proof of impossibility (Conjecture 3)
