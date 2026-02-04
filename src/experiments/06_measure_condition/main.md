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


## Conjectures (Original) and Resolution

### Conjecture 1 (Necessity) - REFINED
Original: If measure condition fails, then T = Omega(1/Delta_*^2).

**Resolution**: PARTIALLY TRUE, but understated. The exact scaling is T = Theta(1/Delta_*^{3 - 2/alpha}) where alpha > 1 is the flatness exponent. For alpha = 2, this gives Theta(1/Delta_*^2). For larger alpha, the scaling is WORSE.

### Conjecture 2 (Dichotomy) - FALSE
Original: Either T = Theta(1/Delta_*) or T = Theta(1/Delta_*^2), nothing in between.

**Resolution**: FALSE. There IS intermediate scaling! The exponent gamma = 3 - 2/alpha forms a continuum from 1 to 3. Example: alpha = 1.5 gives gamma = 5/3, so T = Theta(1/Delta_*^{5/3}).

### Conjecture 3 (Characterization) - PROVEN
Original: Measure condition fails iff gap has flat minimum (alpha > 1).

**Resolution**: TRUE. See Theorem 1 in Results section.


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

**Status**: PROVEN

### Theorem 1 (Geometric Characterization)
The measure condition holds (with C independent of Delta_*) iff the gap approaches its minimum at most linearly. Precisely, for Delta(s) = Delta_* + Theta(|s - s*|^alpha):
- alpha <= 1: Measure condition holds
- alpha > 1: Measure condition fails for small Delta_*

### Theorem 2 (Scaling Spectrum)
The optimal runtime satisfies:
```
T = Theta(1/Delta_*^{3 - 2/alpha})
```

This gives a continuum of scalings:
- alpha = 1 (linear/V-shaped): T = Theta(1/Delta_*)
- alpha = 2 (quartic/flat): T = Theta(1/Delta_*^2)
- alpha = 3: T = Theta(1/Delta_*^{7/3})
- alpha -> infinity: T -> Theta(1/Delta_*^3)

### Dichotomy Correction
**Conjecture 2 is FALSE.** There IS intermediate scaling! The exponent gamma = 3 - 2/alpha ranges continuously from 1 to 3.

However, there IS a sharp transition at alpha = 1: this is the boundary between measure condition holding and failing.


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

**Phase**: COMPLETE (theoretical analysis + Lean formalization)

Completed:
1. Proved geometric characterization (Theorem 1)
2. Derived scaling spectrum formula T = Theta(1/Delta_*^{3-2/alpha}) (Theorem 2)
3. Corrected the dichotomy conjecture (it's a spectrum, not binary)
4. Lean formalization (lean/ directory)
   - No `sorry` statements
   - Only standard axioms (propext, Classical.choice, Quot.sound)
   - Key theorems: `geometric_characterization`, `scaling_spectrum`, `dichotomy_false`

Remaining (optional):
1. Numerical verification of scaling for various alpha
2. Survey which physical systems have which alpha values
3. Connection to computational complexity (does NP-hardness correlate with large alpha?)
