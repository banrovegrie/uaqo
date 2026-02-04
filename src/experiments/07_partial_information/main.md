# Partial Information: The Interpolation Theorem

## Problem Statement

The original paper establishes two extremes:
- **Fully informed**: Knowing A_1 to precision O(2^{-n/2}) gives optimal runtime T_inf = O(sqrt(2^n/d_0))
- **Fully uninformed**: Not knowing A_1 requires T_unf = Omega(2^{n/2} * T_inf) (from experiment 04)

But what happens in between? If you know A_1 to some intermediate precision epsilon, what runtime can you achieve?

**Central Question**: Characterize T(epsilon), the optimal runtime achievable with A_1 known to precision epsilon.


## Why Novel

The paper shows:
- NP-hardness kicks in at precision 1/poly(n)
- Required precision for optimality is 2^{-n/2}
- Gap between these is exponentially large

**Unexplored**: The entire region between 1/poly(n) and 2^{-n/2} precision. This is where practical algorithms might operate - you can't compute A_1 exactly, but you might have some estimate.


## Conjectures

### Conjecture 1 (Smooth Interpolation)
The runtime interpolates smoothly:
```
T(epsilon) = T_inf * max(1, (s_R - s_L) / max(delta_s, epsilon))
```
where delta_s ~ 2^{-n/2} is the crossing width and (s_R - s_L) is the uncertainty in s*.

### Conjecture 2 (Threshold Behavior)
There exists a critical precision epsilon_c such that:
- epsilon < epsilon_c: T(epsilon) = O(T_inf * poly(n))
- epsilon > epsilon_c: T(epsilon) = Omega(T_inf * 2^{alpha * n}) for some alpha > 0

### Conjecture 3 (Graceful Degradation)
For epsilon = O(1/poly(n)), the runtime is:
```
T(epsilon) = T_inf * O(1/epsilon)
```
Linear degradation with inverse precision.


## Approach

### Strategy 1: Direct Error Analysis
Given estimate A_1_est = A_1 + delta with |delta| <= epsilon:
1. Construct schedule using s*_est = A_1_est/(A_1_est + 1)
2. Analyze gap encountered: g(s*_est) vs g_min
3. Compute adiabatic error from schedule misalignment
4. Derive runtime needed to achieve target fidelity

### Strategy 2: Minimax Framework
For precision epsilon, define:
```
G_epsilon = {gap profiles : |s* - s*_est| <= f(epsilon)}
```
Then T(epsilon) is the minimax optimal time:
```
T(epsilon) = min_schedule max_{gap in G_epsilon} T(schedule, gap)
```
This extends the 04 framework to partial information.

### Strategy 3: Numerical Characterization
For small n (up to 20):
1. Fix A_1 precision epsilon
2. Sample gap profiles consistent with the precision
3. Run AQO with estimated schedule
4. Measure fidelity vs runtime
5. Fit the scaling T(epsilon)


## Technical Details

### Error from Misaligned Schedule
If true crossing is at s* and schedule is optimized for s*_est = s* + delta:
- The schedule has velocity v(s) ~ Delta^{3/2}(s*_est) near s*_est
- But the actual minimum gap is at s*, where the schedule has velocity v(s*) ~ Delta^{3/2}(s*_est) != Delta^{3/2}(s*)

The error accumulation depends on:
1. How far delta is from zero
2. The shape of the gap near the minimum
3. The derivative of the gap at the minimum

### Precision-Runtime Tradeoff
From Jansen-Ruskai-Seiler, the error from traversing the crossing region is:
```
error ~ (v_crossing)^2 * delta_s / Delta_*^3
```
If the schedule is misaligned by delta, the effective crossing width becomes max(delta_s, delta), giving:
```
error ~ v^2 * max(delta_s, delta) / Delta_*^3
```
To maintain constant error, we need v ~ Delta_*^{3/2} / sqrt(max(delta_s, delta)), which gives:
```
T ~ max(delta_s, delta) / v ~ sqrt(max(delta_s, delta)) / Delta_*^{3/2}
```

### The Interpolation Formula
This suggests:
```
T(epsilon) / T_inf ~ sqrt(max(1, epsilon/delta_s))
```
For epsilon << delta_s: T(epsilon) ~ T_inf (precision sufficient)
For epsilon >> delta_s: T(epsilon) ~ T_inf * sqrt(epsilon/delta_s) (precision insufficient)


## Results

**Status**: CONJECTURAL

Preliminary analysis suggests smooth interpolation with sqrt scaling. Need to:
1. Make the error analysis rigorous
2. Verify numerically
3. Check if there are phase transitions at special precision levels


## Practical Implications

If Conjecture 3 holds (graceful degradation):
- Even 1/poly(n) precision gives poly(n) overhead, not exponential
- Heuristic estimates of A_1 might be practically useful
- The NP-hardness barrier is "soft" - you pay polynomially, not exponentially


## Open Questions

1. Is the interpolation smooth or are there phase transitions?
2. Does the precision requirement depend on the problem structure?
3. Can randomized estimates (with variance) be useful?
4. What's the optimal allocation of resources between estimating A_1 and running AQO?


## Connection to Other Experiments

- Extends 04 (separation theorem) to partial information
- Informs 05 (adaptive schedules) - measurements give partial information
- Connects to 08 (structured tractability) - some problems might need less precision


## References

1. Original paper - Sections on precision requirements
2. Guo-An 2025 - Error scaling analysis
3. Jansen-Ruskai-Seiler 2007 - Error bounds


## Status

**Phase**: Proposed

Next steps:
1. Rigorous derivation of the precision-runtime tradeoff
2. Numerical validation for small n
3. Check for phase transitions at special precision levels
4. Write up the interpolation theorem
