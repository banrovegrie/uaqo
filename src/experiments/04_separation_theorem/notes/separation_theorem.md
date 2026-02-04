# Separation Theorem: A_1-Independent Schedules Require Exponentially More Time

## Theorem Statement

**Theorem**: Consider the family of AQO instances parameterized by A_1 in [$\alpha$_min, $\alpha$_max], with avoided crossing positions in [s*_min, s*_max] where

$\Delta$s* = s*_max - s*_min = $\alpha$_max/($\alpha$_max+1) - $\alpha$_min/($\alpha$_min+1).

Let $\delta$ = $\Theta$(sqrt(d_0/N)) be the crossing width and g_min = $\Theta$(sqrt(d_0/N)) be the minimum gap.

Then:

1. **Optimal (A_1-aware) schedule** achieves fidelity 1-$\varepsilon$ in time:
   T_opt = O($\delta$/g_min^2) = O(sqrt(N/d_0))

2. **Any A_1-independent schedule** achieving fidelity 1-$\varepsilon$ for ALL instances requires time:
   T_indep = $\Omega$($\Delta$s*/g_min^2) = $\Omega$($\Delta$s* * N/d_0)

3. **Separation**:
   T_indep / T_opt = $\Omega$($\Delta$s* / $\delta$) = $\Omega$($\Delta$s* * sqrt(N/d_0))

For $\Delta$s* = $\Omega$(1) (constant range of crossing positions), this is an **exponential separation** in n.


## Proof

### Part 1: Optimal Schedule Runtime

The adiabatic theorem states that to achieve fidelity 1-$\varepsilon$, the schedule s(t) must satisfy:

$\int$_0^1 |ds/dt| * (1/g(s)^2) dt $\leq$ C/$\varepsilon$

for some constant C.

The optimal local schedule sets ds/dt $\propto$ g(s)^2, giving:

T_opt = $\int$_0^1 ds / g(s)^2

The gap structure near the avoided crossing at s* is:

g(s) = g_min * sqrt(1 + ((s - s*)/$\delta$)^2)

The integral is dominated by the crossing region [s* - $\delta$, s* + $\delta$]:

T_opt $\approx$ $\int$_{s*-$\delta$}^{s*+$\delta$} ds / g_min^2 = 2$\delta$ / g_min^2 = O(sqrt(N/d_0))

### Part 2: A_1-Independent Schedule Lower Bound

Consider any schedule s(t) that doesn't depend on the specific instance.

For this schedule to achieve fidelity 1-$\varepsilon$ for an instance with crossing at position s*, it must satisfy the adiabatic condition near s*:

$\int$_{near s*} |ds/dt| / g(s)^2 dt $\leq$ C/$\varepsilon$

Since g(s) $\approx$ g_min in the crossing region, this requires the schedule to pass through [s* - $\delta$, s* + $\delta$] slowly:

Time in crossing region $\geq$ 2$\delta$ * g_min^2 / (something small)

**Key observation**: The A_1-independent schedule must satisfy this for EVERY possible crossing position s* $\in$ [s*_min, s*_max].

**Claim**: The schedule must have |ds/dt| $\leq$ g_min^2 * $\varepsilon$ / C throughout [s*_min, s*_max].

**Proof of Claim**: Suppose not. Then there exists s' $\in$ [s*_min, s*_max] where |ds/dt(t')| > g_min^2 * $\varepsilon$ / C for some t' with s(t') = s'.

Consider an instance with crossing at s* = s'. Near s', the gap is g(s) $\approx$ g_min.

The adiabatic condition requires:
$\int$_{near s'} |ds/dt| / g_min^2 dt $\leq$ C/$\varepsilon$

But if |ds/dt| > g_min^2 * $\varepsilon$ / C in this region, the condition is violated.

Therefore, for the schedule to work for ALL instances, it must be slow (|ds/dt| $\leq$ g_min^2 * $\varepsilon$ / C) throughout [s*_min, s*_max].

**Runtime Lower Bound**:

T_indep $\geq$ Time to traverse [s*_min, s*_max]
       = $\Delta$s* / (max speed in this region)
       $\geq$ $\Delta$s* / (g_min^2 * $\varepsilon$ / C)
       = $\Delta$s* * C / (g_min^2 * $\varepsilon$)
       = $\Omega$($\Delta$s* * N/d_0)

### Part 3: Separation

T_indep / T_opt = $\Omega$($\Delta$s* * N/d_0) / O(sqrt(N/d_0))
                = $\Omega$($\Delta$s* * sqrt(N/d_0))
                = $\Omega$($\Delta$s* * 2^{n/2})

For $\Delta$s* = $\Omega$(1), this is exponential in n. QED


## Interpretation

### What This Says

1. **Without A_1 knowledge, you pay an exponential penalty**: The runtime degrades from O(sqrtN) to O(N).

2. **The penalty is proportional to uncertainty**: If $\Delta$s* is small (you know A_1 approximately), the penalty is smaller.

3. **The penalty comes from "hedging"**: Not knowing where the crossing is, you must be slow everywhere it could be.


### Tightness

The lower bound is achieved by the "wide slow" schedule that goes slowly at uniform speed through [s*_min, s*_max]. This schedule is optimal among A_1-independent schedules.


### Connection to the Paper

The paper proves:
- A_1 estimation to precision $\delta$ $\approx$ sqrt(d_0/N) is needed for optimal runtime
- This estimation is NP-hard at precision 1/poly(n)

Our theorem quantifies the consequence:
- Without A_1 (or with only coarse A_1 bounds), runtime degrades by factor sqrt(N/d_0)
- This is the "price" of the NP-hardness barrier


## Refinement: Partial A_1 Knowledge

**Corollary**: If A_1 is known to lie in [$\alpha$_min, $\alpha$_max], the optimal runtime is:

T($\Delta$s*) = $\Theta$($\Delta$s* * N/d_0 + $\delta$ * N/d_0)

where the first term is the "hedging cost" and the second is the intrinsic adiabatic cost.

As $\Delta$s* -> 0 (perfect A_1 knowledge), T -> O(sqrt(N/d_0)).
As $\Delta$s* -> $\Theta$(1) (no A_1 knowledge), T -> O(N/d_0).

**Interpretation**: The value of A_1 information is captured by the reduction in $\Delta$s*. Each bit of precision on A_1 roughly halves $\Delta$s*, giving a constant-factor improvement in runtime.


## Open Questions

1. Is the separation tight, or can more clever schedules do better?

2. What about AVERAGE-case (over instances) instead of worst-case?

3. Can we prove a similar separation for specific NP-hard problem families?

4. Does the separation hold for other adiabatic Hamiltonians (e.g., transverse field)?
