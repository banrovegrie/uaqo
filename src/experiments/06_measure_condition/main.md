# Measure Condition: When Does Guo-An Break?

## Problem Statement

Guo-An (2025) proves that power-law scheduling u'(s) proportional to Delta^p(u(s)) achieves quadratically improved error scaling O(1/Delta_*) instead of O(1/Delta_*^2), provided the gap satisfies the **measure condition**:
```
mu({s in [0,1] : Delta(s) <= x}) <= C * x
```
for some constant C > 0.

**Central Questions**:
1. What happens when the measure condition fails?
2. Is the measure condition necessary, or just sufficient?
3. Can we characterize the boundary between O(1/Delta_*) and O(1/Delta_*^2) scaling?


## Why Novel

Guo-An proves:
- Sufficiency: Measure condition implies O(1/Delta_*) with power-law schedule
- Optimality: p = 3/2 is optimal for linear gaps

**What Guo-An does NOT prove**:
- Necessity: Whether measure condition failure implies O(1/Delta_*^2)
- Characterization: Which Hamiltonians violate the measure condition
- Dichotomy: Whether there's a sharp transition

This is unexplored territory that could reveal fundamental structure in the AQO landscape.


## Conjectures

### Conjecture 1 (Necessity)
If the measure condition fails with constant C* (i.e., the infimum of valid C is infinite), then any schedule requires time Omega(1/Delta_*^2).

### Conjecture 2 (Dichotomy)
There is a dichotomy:
- Measure condition holds: optimal schedule achieves O(1/Delta_*)
- Measure condition fails: every schedule requires Omega(1/Delta_*^2)

No intermediate scaling exists.

### Conjecture 3 (Characterization)
The measure condition fails if and only if the gap function has a "flat minimum" - i.e., Delta(s) = Delta_* + O((s - s*)^alpha) with alpha > 1 near the minimum.


## Approach

### Strategy 1: Explicit Construction
Build families of Hamiltonians where measure condition fails:
- Gap functions with flat minima: Delta(s) = Delta_* + (s - s*)^4
- Oscillating gaps that spend long time near minimum
- Random gap functions from suitable ensembles

For each, compute the exact adiabatic error and show it scales as 1/Delta_*^2.

### Strategy 2: Lower Bound via Jansen-Ruskai-Seiler
The JRS error bound contains the integral:
```
integral_0^1 |u''(s)| / Delta^2(u(s)) ds + integral_0^1 (u'(s))^2 / Delta^3(u(s)) ds
```
If measure condition fails, show this integral is Omega(1/Delta_*^2) for any schedule u.

### Strategy 3: Physical Interpretation
The measure condition says the system cannot linger too long near small gaps. Failure means:
- Adiabatic evolution must traverse a "wide" region of small gap
- No schedule can rush through without accumulating O(1/Delta_*^2) error


## Technical Details

### Measure Condition in Guo-An
For gap Delta(s), define:
```
M(x) = mu({s : Delta(s) <= x})
```
Measure condition: M(x) <= C * x for all x > 0.

**Geometric interpretation**: The sublevel sets of Delta have measure at most linear in the threshold.

### When Does It Fail?
The condition fails if M(x) grows faster than linear. Examples:
- Delta(s) = (s - 1/2)^4 + Delta_*: Near s = 1/2, Delta(s) <= Delta_* + epsilon requires |s - 1/2| <= epsilon^{1/4}, so M(Delta_* + epsilon) ~ epsilon^{1/4} >> epsilon
- Oscillating: Delta(s) = Delta_* + epsilon * sin^2(n * s): Many minima, total measure ~ 1/sqrt(epsilon)

### Lower Bound Structure
If measure condition fails, for any schedule u:
```
integral_0^1 (u'(s))^2 / Delta^3(u(s)) ds >= ?
```
Need to show this is Omega(1/Delta_*^2) regardless of u.


## Results

**Status**: CONJECTURAL

No proofs yet. Preliminary observations:
- For Delta(s) = Delta_* + (s - s*)^{2k}, the measure condition holds iff k = 1
- This suggests quadratic minimum is critical


## Open Questions

1. Is there a natural physical interpretation for measure condition failure?
2. Do NP-hard problems encoded in AQO typically satisfy or violate the measure condition?
3. Can measure condition failure be detected efficiently?
4. Is there a hierarchy of conditions beyond measure condition?


## Connection to Other Experiments

- Related to 07 (partial information): Measure condition failure might correlate with A_1 hardness
- Related to 08 (structured tractability): Maybe tractable A_1 implies measure condition?
- Informs understanding of 04 (separation theorem)


## References

1. Guo-An 2025 - Power-law scheduling and measure condition (Section 3.1)
2. Jansen-Ruskai-Seiler 2007 - Adiabatic error bounds (Theorem 3)
3. Jarret-Lackey-Liu-Wan 2019 - Bashful adiabatic algorithm (also uses measure condition)


## Status

**Phase**: Proposed

Next steps:
1. Compute explicit examples where measure condition fails
2. Numerically verify scaling for these examples
3. Attempt lower bound proof via JRS analysis
4. Survey which problem classes satisfy/violate the condition
