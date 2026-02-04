# Information-Theoretic Limits: Beyond the Adiabatic Framework

## Problem Statement

All current hardness results are specific to adiabatic quantum optimization:
- A_1 is hard to compute classically
- The separation theorem (04) bounds fixed adiabatic schedules
- Guo-An's results are about adiabatic error bounds

**Central Question**: Are there fundamental information-theoretic limits that apply to ANY algorithm (quantum or classical, adiabatic or circuit-based) trying to find ground states without spectral information?


## Why Novel

The paper and all follow-up work focus on adiabatic algorithms. But:
- Circuit-model algorithms (Grover, QAOA, variational) don't need A_1
- Classical heuristics (simulated annealing) don't use spectral information
- Is the adiabatic framework uniquely limited, or is there a deeper barrier?

If we prove information-theoretic lower bounds, they would:
1. Unify all existing hardness results
2. Apply to any future algorithm
3. Establish truly fundamental limitations


## Conjectures

### Conjecture 1 (Oracle Lower Bound)
Any algorithm (quantum or classical) that finds the ground state of a random Hamiltonian H_z using oracle access to H_z requires:
```
Omega(sqrt(N/d_0))
```
queries, regardless of what other information is available.

This is the Grover lower bound and should be tight.

### Conjecture 2 (Information-Complexity Tradeoff)
There exists a function f such that for any algorithm achieving runtime T:
```
I(algorithm) >= f(N, d_0, T)
```
where I(algorithm) is the mutual information between the algorithm's internal state and the spectrum of H_z.

### Conjecture 3 (Adiabatic Limitation)
Adiabatic algorithms are uniquely limited: they achieve optimal query complexity O(sqrt(N/d_0)) but require additional O(n) bits of information (A_1 or equivalent) that circuit algorithms get "for free".

### Conjecture 4 (No Free Lunch)
For any algorithm achieving O(sqrt(N/d_0)) runtime without explicit spectral information:
- Either it implicitly computes the spectral information (taking additional time), OR
- It works only for structured problem classes (not general H_z)


## Approach

### Strategy 1: Query Complexity Lower Bound
Frame ground state finding as an oracle problem:
- Oracle O_z: given basis state |x>, returns sign of H_z|x> - E_threshold|x>
- Task: find x in ground space (H_z|x> = E_0|x>)

Use quantum query complexity techniques:
- Polynomial method
- Adversary method
- Recording query technique

### Strategy 2: Communication Complexity
Frame as communication problem:
- Alice has problem instance (H_z)
- Bob wants to output a ground state
- What is the communication complexity?

The A_1 hardness might be a communication lower bound in disguise.

### Strategy 3: Information-Theoretic Framework
Model algorithms as information processors:
- Input: oracle access to H_z
- Internal state: contains information about H_z
- Output: ground state with probability >= 1 - epsilon

Use mutual information, Fisher information, or entropy to bound:
- How much information can be extracted per query
- How much information is needed for the task
- Gap between these = fundamental limitation

### Strategy 4: Compare Algorithm Classes
Systematically compare:
1. Adiabatic algorithms
2. Circuit-model algorithms (Grover, QPE)
3. Variational algorithms (VQE, QAOA)
4. Classical algorithms (simulated annealing, MCMC)

For each, characterize:
- Query complexity
- Additional information needed
- Space complexity
- Success probability


## Technical Details

### The Query Model
Standard quantum query model:
- Oracle O_f: |x>|b> -> |x>|b XOR f(x)>
- For ground state finding: f(x) = 1 iff H_z|x> = E_0|x>

Grover lower bound: Any algorithm needs Omega(sqrt(N/d_0)) queries.

But the adiabatic algorithm uses a different oracle:
- Hamiltonian simulation oracle: e^{-iH_z t}
- This is strictly more powerful than the standard query oracle

### Adiabatic vs Query Oracle
The adiabatic algorithm uses time evolution e^{-iH(s)t}, which includes:
- e^{-i H_0 t} = e^{i |psi_0><psi_0| t}: trivial
- e^{-i H_z t}: requires simulating H_z

Each application of e^{-i H_z t} costs O(1) queries to H_z (for local Hamiltonians). So:
- Adiabatic runtime T translates to O(T) queries
- Query lower bound Omega(sqrt(N/d_0)) implies T >= Omega(sqrt(N/d_0))

This is the known lower bound. The question is what additional information is needed.

### Information Content of A_1
A_1 is a single real number encoding information about all d_k and E_k:
```
A_1 = (1/N) sum_k d_k / (E_k - E_0)
```
Information content: O(n) bits (for polynomial precision)
Full spectrum: O(N * n) = O(n * 2^n) bits

So A_1 is a massive compression of spectral information. The hardness is in computing this compressed representation.


## Results

**Status**: HIGHLY CONJECTURAL

This is the most ambitious direction. No concrete results yet, just framework.


## Challenges

1. Comparing different oracle models is notoriously difficult
2. Information-theoretic bounds often have large constants
3. The "additional information" might not be cleanly quantifiable
4. Circuit algorithms might achieve optimality in ways that don't fit this framework


## Open Questions

1. Is there a clean information-theoretic quantity that characterizes what's needed beyond query access?
2. Do circuit algorithms (Grover, QPE) implicitly "know" A_1?
3. Is the adiabatic limitation an artifact of the continuous-time model?
4. Can we prove unconditional separations between algorithm classes?


## Connection to Other Experiments

- Generalizes all other experiments to arbitrary algorithms
- Would unify 04 (separation), 05 (adaptive), 09 (Guo-An) under one framework
- Most ambitious but also highest risk


## References

1. Query complexity lower bounds (Beals et al., Ambainis)
2. Communication complexity and quantum algorithms
3. Information-theoretic quantum limits
4. Comparison of quantum algorithm models


## Status

**Phase**: Proposed (High Risk / High Reward)

Next steps:
1. Formalize the oracle model precisely
2. Review query complexity lower bound techniques
3. Attempt to prove Conjecture 1 (should be straightforward - it's Grover)
4. Investigate what "additional information" means formally
5. Compare specific algorithms in this framework
