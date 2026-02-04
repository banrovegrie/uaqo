# Theoretical Separation: A_1-Independent Schedules Must Be Suboptimal

## Goal

Prove rigorously that any schedule not depending on A_1 must have worse performance than the optimal A_1-aware schedule.


## Setup

Consider the family of Hamiltonians $H_\alpha$ parameterized by $\alpha \in [\alpha_{\min}, \alpha_{\max}]$:

$$H_\alpha(s) = -(1-s)|\psi_0\rangle\langle\psi_0| + s \cdot H_z^{(\alpha)}$$

where $H_z^{(\alpha)}$ is designed so that $A_1(H_z^{(\alpha)}) = \alpha$.

The avoided crossing position is $s^*_\alpha = \alpha/(\alpha+1)$.


## The Adiabatic Condition

From the adiabatic theorem, to maintain fidelity $1-\varepsilon$, the schedule must satisfy:

$$\int_0^1 |ds/dt| / g(s)^2 \, dt \leq C/\varepsilon$$

where g(s) is the spectral gap and C is a constant.

Rearranging: the total evolution time must satisfy

$$T \geq (C/\varepsilon) \cdot \int_0^1 ds / g(s)^2$$


## Gap Structure

Near the avoided crossing at $s^*_\alpha$:

$$g(s) \approx g_{\min} \cdot \sqrt{1 + ((s - s^*_\alpha)/\delta_\alpha)^2}$$

where:
- $g_{\min} = O(\sqrt{d_0/N})$ is the minimum gap
- $\delta_\alpha = O(\sqrt{d_0/N})$ is the width of the crossing region

Outside the crossing region, $g(s) = \Omega(1)$.


## Optimal Schedule (knowing $\alpha$)

The optimal local schedule slows down only near $s^*_\alpha$:

$$ds/dt \propto g(s)^2$$

This gives total time:

$$T_{\text{opt}}(\alpha) = O(1/g_{\min}^2 \cdot \delta_\alpha) = O(\sqrt{N/d_0})$$


## A_1-Independent Schedule

Now consider any schedule s(t) that doesn't know $\alpha$.

**Key observation**: The schedule must handle ALL possible $\alpha \in [\alpha_{\min}, \alpha_{\max}]$.

The crossing positions span the range:

$$[s^*_{\min}, s^*_{\max}] = [\alpha_{\min}/(\alpha_{\min}+1), \alpha_{\max}/(\alpha_{\max}+1)]$$

Let $\Delta s^* = s^*_{\max} - s^*_{\min}$.


## Lower Bound Argument

**Claim**: Any $A_1$-independent schedule achieving fidelity $1-\varepsilon$ for all $\alpha$ must have runtime at least:

$$T \geq \Omega(\sqrt{N/d_0} \cdot \Delta s^*/\delta)$$

where $\delta = O(\sqrt{d_0/N})$ is the crossing width.


**Proof sketch**:

1. The schedule must slow down enough near $s^*_\alpha$ for EVERY $\alpha$ in the range.

2. Since the schedule doesn't know $\alpha$, it must slow down over the ENTIRE interval $[s^*_{\min}, s^*_{\max}]$.

3. In this interval, the gap could be as small as $g_{\min}$ for some $\alpha$.

4. The time spent in this interval must satisfy:

   $$T_{\text{interval}} \geq (\Delta s^*) \cdot 1/g_{\min}^2 = \Delta s^* \cdot N/d_0$$

5. Wait, this is too pessimistic. Let me reconsider...

Actually, the gap is only small near the TRUE $s^*_\alpha$, not everywhere in $[s^*_{\min}, s^*_{\max}]$.

For a given $\alpha$, the gap is small only in $[s^*_\alpha - \delta, s^*_\alpha + \delta]$.


**Revised argument**:

Consider a discrete set of $\alpha$ values: $\alpha_1, \alpha_2, \ldots, \alpha_k$ with corresponding $s^*_1, s^*_2, \ldots, s^*_k$.

Choose them so that the crossing regions are disjoint:
$$s^*_{i+1} - s^*_i > 2\delta$$

The number of such disjoint crossings is:
$$k = \Omega(\Delta s^* / \delta) = \Omega(\Delta s^* \cdot \sqrt{N/d_0})$$

For an $A_1$-independent schedule:
- It doesn't know which $\alpha_i$ is the true parameter
- It must achieve fidelity $1-\varepsilon$ for ALL $\alpha_i$

**Key lemma**: If a schedule achieves fidelity $1-\varepsilon$ for instance with crossing at $s^*_i$, it must spend time $\Omega(1/g_{\min}^2 \cdot \delta)$ in the interval $[s^*_i - \delta, s^*_i + \delta]$.

**Proof**: The adiabatic condition requires $\int |ds/dt| / g(s)^2 \, dt \leq C/\varepsilon$ near the crossing. Since $g(s) \approx g_{\min}$ in this region, we need time $\Omega(\delta/g_{\min}^2)$.

**Lower bound**: An $A_1$-independent schedule must spend time $\Omega(\delta/g_{\min}^2)$ near EACH of the k possible crossings.

But wait - this isn't right either. The schedule can spend most of its time near one crossing and still achieve high fidelity for that instance. The other instances would fail.

**Correct formulation**:

For an $A_1$-independent schedule to achieve fidelity $1-\varepsilon$ for ALL instances, consider the "worst-case" instance.

Given schedule s(t), define:

$$f(s) = \int_{t: s(t) \in [s-\delta, s+\delta]} dt / g_{\min}^2$$

This measures how much "adiabaticity budget" is allocated to position s.

For fidelity $1-\varepsilon$ at instance with $s^*_i = s$, we need $f(s) \geq C/\varepsilon$.

If we want fidelity $1-\varepsilon$ for ALL instances (all $s^*_i$), we need:

$$f(s^*_i) \geq C/\varepsilon \text{ for all } i$$

The total time is:
$$T = \int_0^T dt \geq \sum_i (\text{time in } [s^*_i - \delta, s^*_i + \delta])$$

If the crossing regions are disjoint (which we can arrange), these intervals don't overlap.

Therefore:
$$T \geq k \cdot (\delta/g_{\min}^2) \cdot (C/\varepsilon)$$
$$= \Omega(\Delta s^*/\delta) \cdot \delta/g_{\min}^2$$
$$= \Omega(\Delta s^* / g_{\min}^2)$$
$$= \Omega(\Delta s^* \cdot N/d_0)$$


**Comparison to optimal**:

Optimal (knowing $\alpha$): $T_{\text{opt}} = O(\sqrt{N/d_0})$

$A_1$-independent: $T_{\text{indep}} \geq \Omega(\Delta s^* \cdot N/d_0)$

**Separation**:

$$T_{\text{indep}} / T_{\text{opt}} \geq \Omega(\Delta s^* \cdot \sqrt{N/d_0})$$

For $\Delta s^* = \Omega(1)$ (reasonable range of $A_1$ values), this is:

$$T_{\text{indep}} / T_{\text{opt}} \geq \Omega(\sqrt{N/d_0}) = \Omega(2^{n/2})$$

**This is an exponential separation!**


## Theorem Statement

**Theorem**: Let $[\alpha_{\min}, \alpha_{\max}]$ be a range of $A_1$ values with

$$\Delta s^* = \alpha_{\max}/(\alpha_{\max}+1) - \alpha_{\min}/(\alpha_{\min}+1) = \Omega(1).$$

Any schedule s(t) that achieves fidelity $1-\varepsilon$ for ALL instances with $A_1 \in [\alpha_{\min}, \alpha_{\max}]$ must have runtime:

$$T \geq \Omega((\Delta s^*/\varepsilon) \cdot N/d_0)$$

In contrast, the optimal $A_1$-aware schedule achieves fidelity $1-\varepsilon$ in time:

$$T_{\text{opt}} = O((1/\varepsilon) \cdot \sqrt{N/d_0})$$

The separation is $\Omega(\Delta s^* \cdot \sqrt{N/d_0})$, which is exponential in n for constant $\Delta s^*$.


## Interpretation

This theorem says:
1. **$A_1$ knowledge is exponentially valuable** for worst-case runtime
2. Without knowing $A_1$, you must "hedge" across all possible crossings
3. The cost of hedging is proportional to the uncertainty range $\Delta s^*$


## Caveats

1. This is a WORST-CASE result. For typical instances, the separation may be smaller.

2. The argument assumes you want fidelity $1-\varepsilon$ for ALL instances. If you only care about EXPECTED fidelity, the result changes.

3. The lower bound might be loose - a tighter analysis could sharpen it.


## Connection to the Paper

The paper proves:
- Optimal schedule requires knowing $A_1$ to precision $\delta_s \approx \sqrt{d_0/N}$
- Computing $A_1$ to this precision is NP-hard

Our theorem adds:
- WITHOUT this knowledge, the runtime degrades by factor $\sqrt{N/d_0}$
- This quantifies the "cost" of the NP-hardness barrier


## What Remains

1. Formalize the proof (make the adiabatic theorem application rigorous)
2. Check if the lower bound is tight
3. Consider average-case instead of worst-case
4. Relate to specific problem families (not just parameterized instances)
