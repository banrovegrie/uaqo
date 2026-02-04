# Message for Shantanav (Revised)

Subject: Sanity check on a minimax result for gap-uninformed schedules

---

Hi Shantanav,

I've been exploring a theorem connecting your NP-hardness result with Guo-An's optimality results. After some self-critique, I think I have the framing right, but want your assessment.

**The result (pure minimax, no complexity theory):**

For fixed schedules that must work for all instances in a class C where the gap minimum can be at any s* in [s_L, s_R]:

```
max_{H in C} T(u, H) / T_opt(H) >= (s_R - s_L) / delta_s
```

For Ising Hamiltonians: this ratio is Omega(2^{n/2}).

**The argument:**

1. Adversary sees the schedule u, then picks H in C to place the gap minimum where u is fastest.

2. If u is fast anywhere in [s_L, s_R], adversary exploits it.

3. Therefore u must be slow (velocity ~ Delta_*^2) throughout [s_L, s_R].

4. This takes time Omega((s_R - s_L) / Delta_*^2), vs O(1/Delta_*) for gap-informed.

**Connection to NP-hardness (observation, not theorem):**

The NP-hardness of computing A_1 implies that poly-time preprocessing cannot determine s*. Therefore, algorithms with fixed schedules are forced into the gap-uninformed model and subject to this bound.

This is NOT "NP-hardness implies 2^{n/2} slowdown." It's:
- NP-hardness forces the gap-uninformed model
- The gap-uninformed model has a minimax lower bound
- Therefore this class of algorithms pays the penalty

**Contrast with adaptive:**

Han-Park-Choi 2025 achieves O(1/Delta_*) without prior spectral knowledge via adaptive probing. The minimax bound only applies to fixed schedules.

**My questions:**

1. Is the pure minimax result (Level 1) already known or folklore?

2. Is the connection to NP-hardness (Level 2) correctly stated? I'm NOT claiming the bound follows from NP-hardness, only that NP-hardness justifies the model.

3. Is the gap class G (Ising Hamiltonians with varying A_1) well-defined? Does A_1 actually range over [Omega(1), O(poly(n))] as stated in the paper?

4. Is this worth developing further, or is it too simple an observation?

Thanks,
Alapan

---

## Key improvements over first draft:
- Separated minimax theorem from complexity connection
- Explicitly NOT claiming NP-hardness implies the bound
- Clearer about what is claimed and what is observation
- Contrasted with adaptive methods
