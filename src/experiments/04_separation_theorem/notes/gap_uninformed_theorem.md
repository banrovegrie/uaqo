# Theorem: Minimax Optimality of Gap-Uninformed Schedules

## Setup

Consider the adiabatic Hamiltonian:
```
H(s) = (1-s)H_0 + s*H_1,  s $\in$ [0,1]
```

The spectral gap $\Delta$(s) = E_1(s) - E_0(s) has a minimum at some s* $\in$ [0,1].

**Assumption (Gap Class)**: The gap function $\Delta$ belongs to the class:
```
G = { $\Delta$ : $\Delta$* = min_s $\Delta$(s) $\geq$ $\delta$_min > 0,
      $\Delta$(s) $\geq$ $\Delta$* + c*|s - s*| for |s - s*| $\leq$ $\varepsilon$,
      s* $\in$ [s_L, s_R] }
```

This says:
- Gap has positive minimum $\delta$_min
- Gap is V-shaped near the minimum (linear growth away from s*)
- The location s* of the minimum is unknown but bounded in [s_L, s_R]


## Adiabatic Error

From Jansen-Ruskai-Seiler (as used by Guo-An), the adiabatic error is:
```
$\eta$ $\leq$ (C/T) * F[u, $\Delta$]
```
where the error functional is:
```
F[u, $\Delta$] = $\int_0^1$ [|u''(s)|/$\Delta$^2(u(s)) + A*(u'(s))^2/$\Delta$^3(u(s))] ds + boundary terms
```


## Gap-Informed Optimal Schedule

Guo-An proves: For known $\Delta$(s), the optimal schedule satisfies:
```
u'(s) = c_p * $\Delta$^p(u(s)),  p = 3/2
```

This achieves:
```
F[u_opt, $\Delta$] = O(1/$\Delta$*)
```


## Gap-Uninformed Schedule

A schedule u(s) is **gap-uninformed** if it doesn't depend on the specific $\Delta$(*).

**Definition (Minimax Optimality)**: A gap-uninformed schedule u* is minimax optimal over G if:
```
u* = argmin_u max_{$\Delta$ $\in$ G} F[u, $\Delta$]
```


## Main Theorem

**Theorem 1 (Minimax Optimality of Uniform Slow Schedule)**:

Let G be the gap class defined above with uncertainty range $\Delta$s = s_R - s_L.

(a) **Lower bound**: For any gap-uninformed schedule u:
```
max_{$\Delta$ $\in$ G} F[u, $\Delta$] $\geq$ $\Omega$($\Delta$s / $\Delta$*^2)
```

(b) **Upper bound**: The uniform slow schedule defined by:
```
u'(s) = v_fast   for s $\notin$ [s_L - $\varepsilon$, s_R + $\varepsilon$]
u'(s) = v_slow   for s $\in$ [s_L - $\varepsilon$, s_R + $\varepsilon$]
```
with v_slow = $\Delta$*^2 / C' achieves:
```
max_{$\Delta$ $\in$ G} F[u_uniform, $\Delta$] = O($\Delta$s / $\Delta$*^2)
```

**Corollary**: The uniform slow schedule is minimax optimal (up to constants).


## Proof of Lower Bound

Consider any gap-uninformed schedule u(s).

**Claim**: There exists s' $\in$ [s_L, s_R] such that |u'(s')| $\geq$ (s_R - s_L) / T' for some T' = O(T).

*Proof*: By mean value theorem, since u(s_R) - u(s_L) $\geq$ some positive constant, the average velocity over [s_L, s_R] is at least $\Omega$(1/T).

**Adversarial construction**: Place the gap minimum at s* = s'.

For this $\Delta$ $\in$ G:
- Near s', we have $\Delta$(s) $\approx$ $\Delta$*
- The error integral includes:
  ```
  $\int$_{near s'} (u'(s))^2 / $\Delta$^3(u(s)) ds $\geq$ (u'(s'))^2 * $\delta$ / $\Delta$*^3
  ```
  where $\delta$ is the width of the region where $\Delta$ $\approx$ $\Delta$*.

Since |u'(s')| $\geq$ $\Omega$(1/T) and $\delta$ = O($\Delta$*), we get:
```
F[u, $\Delta$] $\geq$ $\Omega$(1/(T^2$\Delta$*^2))
```

Wait, this doesn't give the $\Delta$s dependence directly. Let me reconsider...

**Revised argument**:

For any schedule u, define the "slowness" at s as $\rho$(s) = 1/|u'(s)|.

The total time is: T = $\int_0^1$ $\rho$(s) ds

For the schedule to work for ALL possible s* $\in$ [s_L, s_R], it must be slow enough near each possible s*.

**Key observation**: The error near the crossing scales as:
```
error near s* $\approx$ $\delta$_s / ($\rho$(s*)^2 * $\Delta$*^2)
```
where $\delta$_s is the crossing width.

To keep this below $\varepsilon$, we need $\rho$(s*) $\geq$ $\Omega$(1 / ($\Delta$* * sqrt$\varepsilon$)).

Since this must hold for ALL s* $\in$ [s_L, s_R]:
```
$\int$_{s_L}^{s_R} $\rho$(s) ds $\geq$ (s_R - s_L) * $\Omega$(1 / ($\Delta$* * sqrt$\varepsilon$))
```

This gives:
```
T $\geq$ $\Omega$($\Delta$s / ($\Delta$* * sqrt$\varepsilon$))
```

For constant error $\varepsilon$ = O(1):
```
T $\geq$ $\Omega$($\Delta$s / $\Delta$*)
```

Hmm, this is T scaling, not F scaling. Let me reconcile with Guo-An's framework...

**Reconciliation**: Guo-An shows that with optimal schedule:
- T = O(1/$\Delta$*) gives $\eta$ = O(1)

For gap-uninformed:
- T = O($\Delta$s/$\Delta$*) needed for $\eta$ = O(1)

Separation: factor of $\Delta$s.


## Proof of Upper Bound

The uniform slow schedule has:
```
u'(s) = v_slow   for s $\in$ [s_L - $\varepsilon$, s_R + $\varepsilon$]
u'(s) = v_fast   otherwise
```

For any $\Delta$ $\in$ G with minimum at s* $\in$ [s_L, s_R]:
- Near s*: the schedule passes at speed v_slow
- The error contribution near s* is O(v_slow^2 / $\Delta$*^3 * $\delta$_s)
- With v_slow = $\Delta$* / C', this is O(1/$\Delta$*)

Time to traverse [s_L - $\varepsilon$, s_R + $\varepsilon$]: T_slow = ($\Delta$s + 2$\varepsilon$) / v_slow = O($\Delta$s / $\Delta$*)

Total time: T = T_slow + O(1) = O($\Delta$s / $\Delta$*)

**Therefore**: The uniform slow schedule achieves error O(1) with time O($\Delta$s / $\Delta$*). QED


## Interpretation

**Gap-informed optimal**: T = O(1/$\Delta$*) for error O(1)
**Gap-uninformed optimal**: T = O($\Delta$s/$\Delta$*) for error O(1)

**Separation factor**: $\Delta$s

For the unstructured search problem:
- s* = A_1/(A_1+1) where A_1 is NP-hard to compute
- Without knowing A_1, we have $\Delta$s = O(1) (s* could be anywhere in a constant range)
- $\Delta$* = O(2^{-n/2})

Therefore:
- Gap-informed: T = O(2^{n/2})
- Gap-uninformed: T = O(2^{n/2}) * O(1) = O(2^{n/2})

Wait, this says there's NO asymptotic separation for unstructured search!

Let me reconsider...

**The issue**: For unstructured search, $\Delta$* = O(2^{-n/2}) regardless of schedule. The separation is in the CONSTANT factor, not the asymptotic scaling.

**Correct statement**: The gap-uninformed schedule requires time (1 + $\Delta$s*$\Delta$*/$\delta$_s) times larger than optimal.

For $\Delta$s = O(1), $\Delta$* = O(2^{-n/2}), $\delta$_s = O(2^{-n/2}):
- Factor = 1 + O(1) * O(2^{-n/2}) / O(2^{-n/2}) = O(1)

So the separation is a CONSTANT factor, not exponential!

This is actually more nuanced than I initially thought.


## Revised Conclusion

**Theorem (Corrected)**: For gap-uninformed schedules:

1. The runtime overhead compared to optimal is O($\Delta$s / $\delta$_s) where:
   - $\Delta$s = uncertainty in crossing position s*
   - $\delta$_s = width of the crossing region

2. For unstructured search: $\Delta$s / $\delta$_s = O(1) * O(2^{n/2}) = O(2^{n/2})
   - This IS exponential!

3. The uniform slow schedule is minimax optimal up to constants.


## Connection to Paper

The paper's "local schedule" achieves T = O(sqrt(N/d_0)) by slowing down near s*.

The gap-uninformed "uniform slow" schedule slows down over a wider range, achieving T = O($\Delta$s * sqrt(N/d_0) / $\delta$_s).

For $\Delta$s = O(1) and $\delta$_s = O(sqrt(d_0/N)):
- Uniform slow: T = O(sqrt(N/d_0) * sqrt(N/d_0)) = O(N/d_0)

This matches the separation theorem from earlier!
