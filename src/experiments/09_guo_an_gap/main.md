# Guo-An Gap: The Missing Circularity

## Problem Statement

Guo-An (2025) proves that power-law scheduling achieves optimal gap dependence O(1/Delta_*) when:
```
u'(s) = c_p * Delta^p(u(s))
```
with p = 3/2 optimal for linear gaps.

**The Problem**: This requires knowing Delta(s), the spectral gap as a function of s. But computing Delta(s) requires diagonalizing H(s) for all s, which is at least as hard as computing A_1!

**Central Question**: Does the Guo-An framework face the same hardness barrier as the original paper? Is computing the optimal schedule itself NP-hard?


## Why Novel

Guo-An's paper focuses on proving optimality of power-law schedules but does not address the computational complexity of constructing them. They briefly mention:
> "implementing the power-law scheduling requires a priori knowledge on the spectral gap, which is a big assumption involving another QMA-hard computational task."

But they don't formalize this or prove hardness. This gap in their analysis needs to be addressed.


## Conjectures

### Conjecture 1 (Schedule Hardness)
Computing the optimal Guo-An schedule (the function u(s) satisfying u'(s) = c_p * Delta^p(u(s))) to sufficient precision is NP-hard.

### Conjecture 2 (Equivalence)
Computing the optimal schedule is computationally equivalent to computing A_1:
- Knowing A_1 to precision epsilon implies knowing the schedule to precision f(epsilon)
- Knowing the schedule to precision delta implies knowing A_1 to precision g(delta)

### Conjecture 3 (Delta vs A_1)
Computing Delta_* (the minimum gap) is strictly harder than computing A_1. Specifically:
- A_1 can be computed from Delta(s) in poly time
- Delta(s) cannot be computed from A_1 alone


## Approach

### Strategy 1: Reduction from A_1
Show that any algorithm computing the Guo-An schedule can be used to compute A_1:
1. Given schedule u(s), we know u'(s) ~ Delta^{3/2}(u(s))
2. The minimum of u'(s) occurs at s* where Delta is minimum
3. Delta_* can be extracted from min u'(s)
4. With Delta_* and s*, we can back-compute A_1

If this reduction works, schedule computation is at least as hard as A_1 computation.

### Strategy 2: Direct Hardness Proof
Prove that approximating Delta(s) to sufficient precision is NP-hard:
1. The minimum gap Delta_* determines the crossing position
2. Computing Delta_* requires finding the minimum eigenvalue gap
3. This is a ground state energy problem for the Hamiltonian "H(s) - first excited state"

### Strategy 3: Information Requirements
Characterize exactly what information about H_z is needed to construct the schedule:
- Guo-An requires Delta(u) for all u in [0,1]
- Original paper requires A_1 (a single number)
- Which is more/less information?


## Technical Details

### What Does Guo-An Actually Need?
To implement power-law scheduling, one needs to solve the ODE:
```
u'(s) = c_p * Delta^p(u(s)), u(0) = 0, u(1) = 1
```
where c_p = integral_0^1 Delta^{-p}(u) du.

This requires:
1. Knowing Delta(u) for u in [0,1] (the gap as a function of the interpolation parameter)
2. Computing the integral c_p
3. Solving the ODE numerically

### Gap Computation Complexity
For H(s) = -(1-s)|psi_0><psi_0| + s*H_z:
- The ground state energy lambda_0(s) can be computed by finding minimum eigenvalue
- The first excited energy lambda_1(s) requires finding second minimum eigenvalue
- Delta(s) = lambda_1(s) - lambda_0(s)

Computing lambda_0(s) for arbitrary s is already a ground state problem. Computing lambda_1(s) is harder (need to constrain to orthogonal complement).

### Connection to A_1
From the paper, the crossing position is s* = A_1/(A_1+1), which is where Delta(s) is minimized. So:
- Knowing where Delta(s) is minimized gives A_1
- Conversely, knowing A_1 gives the position of minimum but not Delta(s) everywhere

### The Circularity
To achieve optimal runtime via Guo-An:
1. Need to construct power-law schedule
2. This requires Delta(s) for all s
3. Computing Delta(s) requires diagonalizing H(s)
4. For general H_z, this takes O(2^n) time classically
5. But we wanted O(2^{n/2}) total time!

So the schedule construction itself might dominate the runtime.


## Results

**Status**: CONJECTURAL

The circularity seems clear informally, but no formal hardness proof yet.


## Implications

If Conjecture 1 is true:
- Guo-An's optimality result is "conditional" on having oracle access to Delta(s)
- The original paper's hardness barrier extends to the Guo-An framework
- Any attempt to achieve O(1/Delta_*) scaling must face the same NP-hardness

If Conjecture 3 is true:
- The original paper's A_1 is actually the "minimal information" needed
- Guo-An's Delta(s) is strictly more information than necessary
- There might be intermediate information levels to explore


## Open Questions

1. Can Delta_* be computed without computing Delta(s) everywhere?
2. Is there a schedule that achieves O(1/Delta_*) using only A_1?
3. For specific problem classes, is Delta(s) easier than general?
4. Can the schedule be learned adaptively during evolution?


## Connection to Other Experiments

- Unifies hardness results with Guo-An framework
- Connects to 05 (adaptive schedules) - can we learn Delta(s) adaptively?
- Connects to 08 (tractability) - maybe Delta(s) tractable for structured problems?


## References

1. Guo-An 2025 - Power-law scheduling (especially Sections 1.1, 3.2)
2. Original paper - A_1 hardness proofs
3. QMA-hardness of ground state energy estimation


## Status

**Phase**: Proposed

Next steps:
1. Formalize the reduction from schedule to A_1
2. Investigate whether Delta_* alone suffices (not full Delta(s))
3. Check if Guo-An's specific applications (Grover, QLSP) have tractable schedules
4. Attempt direct NP-hardness proof for schedule computation
