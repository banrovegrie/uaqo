# TODO: Gap-Uninformed Separation Theorem

## The Theorem to Prove

**Theorem**: For adiabatic evolution with gap minimum at unknown s* in [s_L, s_R]:

```
T_uninformed / T_informed >= (s_R - s_L) / delta_s
```

For unstructured search: this ratio is Omega(2^{n/2}).


## Novelty (Verified)

| Paper | What they do | What they don't |
|-------|-------------|-----------------|
| Original (2025) | Prove A_1 hardness | Quantify runtime cost |
| Guo-An (2025) | Optimal informed schedule | Address uninformed case |
| Matsuura et al. (2021) | Variational method | Prove separation |
| Shingu-Hatomura (2025) | Geometrical method | Prove optimality |
| Nayak 2011 | Adaptive probing | Fixed schedule bounds |
| Han-Park-Choi 2025 | Constant speed (adaptive) | Fixed schedule bounds |

**Our contribution fills the gap: prove FUNDAMENTAL LIMITS on fixed uninformed schedules.**


## Proof Steps

### Step 1: Define gap class G
- [x] Formalize: Delta in G iff Delta has unique minimum at s* in [s_L, s_R] with Delta* >= delta_min
- [x] Include measure condition for applicability of Guo-An bounds

### Step 2: Lower bound (adversarial argument)
- [x] For any schedule u, find s' where u is "fastest" in [s_L, s_R]
- [x] Construct gap Delta in G with minimum at s* = s'
- [x] Apply Jansen-Ruskai-Seiler error bound
- [x] Conclude: u must be slow throughout [s_L, s_R]

### Step 3: Upper bound (uniform slow schedule)
- [x] Define uniform slow: constant velocity in [s_L, s_R]
- [x] Show it achieves the lower bound (up to constants)
- [x] Conclude: uniform slow is minimax optimal

### Step 4: Apply to unstructured search
- [x] Identify s_L, s_R from A_1 range (Theta(1) uncertainty)
- [x] Use delta_s = O(Delta_*) = O(2^{-n/2})
- [x] Get separation Omega(2^{n/2})


## Tools

- [x] Read Jansen-Ruskai-Seiler (2007) for adiabatic error bounds - via Guo-An Lemma 2.1
- [x] Use Guo-An variational framework as template
- [ ] Consider Lean formalization for rigor (optional, for future work)


## Files

- `04_separation_theorem/main_theorem.md` - Theorem statement and proof sketch
- `04_separation_theorem/formal_proof.md` - Complete formal proof with literature verification
- `archive/` - Previous explorations (for reference)


## Success Criteria

1. [x] Theorem statement is precise and unambiguous
2. [x] Proof is complete (no gaps in logic)
3. [x] Verified not in prior literature (7 papers checked)
4. [x] Significance is clear (quantifies NP-hardness cost)


## Remaining Refinements

- [ ] Make constants explicit (track C from Jansen-Ruskai-Seiler)
- [ ] Extend to partial information (knowing A_1 to precision epsilon)
- [ ] Write Lean formalization (long-term)


## Status: PROOF COMPLETE

The Gap-Uninformed Separation Theorem has been proven. The key results:

1. **Lower bound**: Any fixed uninformed schedule requires T >= (s_R - s_L) / Delta_*^2
2. **Upper bound**: Uniform slow schedule achieves this bound
3. **Separation**: T_unf / T_inf = (s_R - s_L) / delta_s = Omega(2^{n/2}) for unstructured search
4. **Novelty verified**: No prior work proves this result (7 papers checked)
