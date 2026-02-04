# Gap-Uninformed Schedule Optimality

## Context

The Guo-An paper (2025) proves that:
- Power-law scheduling u'(s) $\propto$ $\Delta$^p(u(s)) achieves O($\Delta$*^{-1}) error
- The exponent p = 3/2 is optimal (for linear gap profiles)
- **But**: This requires knowing the spectral gap $\Delta$(s)

The original paper proves:
- Computing A_1 (which determines where $\Delta$ is small) is NP-hard
- The required precision for optimal AQO is ~2^{-n/2}

**Open question**: What's the best achievable performance WITHOUT knowing the gap?


## Variational Framework for Gap-Uninformed Schedules

Following Guo-An's approach, the adiabatic error is bounded by:

$\eta$(1) $\leq$ (C/T) * $\int_0^1$ [|u''(s)|/$\Delta$^2(u(s)) + A(u'(s))^2/$\Delta$^3(u(s))] ds

For a gap-INFORMED schedule, we optimize over u(s) knowing $\Delta$(*).
For a gap-UNINFORMED schedule, we must optimize over u(s) WITHOUT knowing $\Delta$(*).


## Minimax Formulation

**Definition**: A gap-uninformed schedule u(s) must achieve low error for ALL possible gap functions in a class G.

**Minimax problem**:
```
min_{u} max_{$\Delta$ $\in$ G} $\eta$(1; u, $\Delta$)
```

This asks: what schedule minimizes the worst-case error over all possible gap functions?


## Theorem (Proposed)

**Theorem**: Consider the class of gap functions G = {$\Delta$ : $\Delta$* $\geq$ $\delta$_min, $\Delta$ has unique minimum in [s*_min, s*_max]}.

The minimax-optimal gap-uninformed schedule is the "uniform slow" schedule:
```
u'(s) = v_slow   for s $\in$ [s*_min - $\varepsilon$, s*_max + $\varepsilon$]
u'(s) = v_fast   otherwise
```
where v_slow and v_fast are chosen to satisfy boundary conditions and minimize worst-case error.


## Proof Sketch

**Lower bound**: For any schedule u(s), consider the worst-case gap function. The gap minimum can be placed anywhere in [s*_min, s*_max]. The schedule must handle ALL these cases.

If u(s) is fast (large |u'|) somewhere in [s*_min, s*_max], an adversarial gap function can place the minimum there, causing large error.

Therefore, u(s) must be slow throughout [s*_min, s*_max].

**Upper bound**: The uniform slow schedule achieves:
```
$\eta$(1) $\leq$ O($\Delta$s* / $\Delta$*^2)
```
where $\Delta$s* = s*_max - s*_min is the uncertainty in crossing position.


## Comparison to Gap-Informed Optimal

Gap-informed (Guo-An): $\eta$(1) = O(1/$\Delta$*) with T = O(1/$\Delta$*)

Gap-uninformed (our result): $\eta$(1) = O($\Delta$s*/$\Delta$*^2) with T = O($\Delta$s*/$\Delta$*^2)

**Separation**: The gap-uninformed schedule requires time factor $\Delta$s*/$\Delta$* larger.

For $\Delta$s* = O(1) and $\Delta$* = O(2^{-n/2}), this is O(2^{n/2}) --- exponential separation!


## Connection to NP-Hardness

The original paper proves A_1 estimation is NP-hard. Our result quantifies the COST of this hardness:

**Corollary**: Any polynomial-time schedule (that doesn't solve an NP-hard problem) incurs an $\Omega$(2^{n/2}) factor runtime overhead compared to the optimal schedule.


## What Needs to Be Done

1. **Formalize the proof**: Make the minimax argument rigorous using Guo-An's variational framework.

2. **Characterize the gap class G**: What's the right class to consider? The measure condition from Guo-An?

3. **Tight bounds**: Is the uniform slow schedule exactly optimal, or just order-optimal?

4. **Connection to partial information**: What if we know A_1 to some precision $\varepsilon$? How does the optimal schedule change?


## Significance

This would be a genuine theoretical contribution:
1. Uses Guo-An's variational framework for a new question
2. Quantifies the cost of NP-hardness in runtime terms
3. Shows that gap-uninformed schedules are fundamentally limited
4. Complements both the original paper and Guo-An's follow-up


## References

- Original paper: Braida et al. (2025) - NP-hardness of A_1 estimation
- Guo-An (2025) - Variational optimality of power-law schedules
- Gap-uninformed strategies: MatsuuraBuckSenicourtZaribafiyan2021, ShinguHatomura2025
