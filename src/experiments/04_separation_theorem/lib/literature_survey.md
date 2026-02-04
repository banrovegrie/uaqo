# Literature Survey: Gap-Uninformed Schedule Lower Bounds

## Summary

Extensive search conducted 2026-02-04. No prior work proves minimax lower bounds for fixed gap-uninformed adiabatic schedules.

## Papers Checked

### Foundational Adiabatic Papers

**Roland-Cerf 2002** - "Quantum Search by Local Adiabatic Evolution"
- Result: Local adiabatic evolution achieves O(sqrt(N)) by adapting schedule to gap
- Gap knowledge: REQUIRED - uses analytic formula for g(s)
- Lower bounds: None for uninformed case
- Key quote: "This speed up was achieved by switching the Hamiltonian according to [formula], which is only possible because here the gap g(s) can be derived analytically"

**van Dam-Mosca-Vazirani 2001** - "How Powerful is Adiabatic Quantum Computation?"
- Result: Variable delay schedule achieves quadratic speedup; exponential lower bound for perturbed Hamming weight
- Gap knowledge: Uses gap function g(s) for variable delay
- Lower bounds: For specific problem structure, not for uninformed schedules
- Relevance: Shows gap-informed vs constant-rate is O(sqrt(N)) vs O(N)

**Jansen-Ruskai-Seiler 2007** - "Bounds for the Adiabatic Approximation"
- Result: Rigorous error bounds with explicit gap dependence
- Gap knowledge: Required for optimal scheduling
- Lower bounds: Error bounds only, not schedule lower bounds
- Key insight: Second-order terms can be O(1/g^6), so tau ~ g^(-3) may be needed
- Relevance: Provides the error analysis used in separation theorem

### Recent Schedule Optimization Papers

**Guo-An 2025** (arXiv:2512.10329) - "Improved Gap Dependence by Adaptive Schedule"
- Result: Power-law scheduling with p=3/2 achieves O(1/Delta) scaling
- Gap knowledge: REQUIRED - "implementing power-law scheduling requires a priori knowledge on the spectral gap"
- Lower bounds: None
- Key quote: Computing spectral gap is QMA-hard in general

**Han-Park-Choi 2025** (arXiv:2510.01923) - "Constant Speed Schedule"
- Result: Achieves O(1/Delta) without prior spectral knowledge
- Method: ADAPTIVE - computes eigenstate overlaps on-the-fly during evolution
- Lower bounds: None
- Key distinction: This is ADAPTIVE, not FIXED. Our theorem addresses fixed schedules.

**Shingu-Hatomura 2025** (arXiv:2501.11846) - "Geometrical Scheduling"
- Result: Schedule construction without full spectra
- Method: Constructive
- Lower bounds: None

**Matsuura et al. 2021** (arXiv:2003.09913) - "Variational Schedule Optimization"
- Result: Variational method for finding schedules
- Method: Constructive
- Lower bounds: None

### Quantum Speed Limit Papers

**Garcia-Pintos et al. 2024** (arXiv:2410.14779) - "Tighter Lower Bounds on Quantum Annealing Times"
- Result: Schedule-INDEPENDENT lower bounds via quantum speed limits
- Type: Fundamental physics limits, not schedule-dependent bounds
- Gap knowledge: Not relevant (bounds hold for all schedules)
- Distinction: Different question - these are absolute limits, not uninformed vs informed comparison

**Phys. Rev. Research 5, 033175 (2023)** - "Lower Bounds by Quantum Speed Limits"
- Result: Necessary conditions for adiabatic algorithms
- Type: Schedule-independent
- Distinction: Complements sufficient conditions, doesn't address uninformed scheduling

### Adaptive/Probing Methods

**Nayak et al. 2011** (arXiv:1105.1707) - "Staying Adiabatic with Unknown Gap"
- Result: Probes gap DURING evolution
- Method: Adaptive
- Distinction: Different model than fixed uninformed schedules

### Hardness Results

**UAQO Paper (Chaudhuri et al. 2025)** - "Unstructured Adiabatic Quantum Optimization"
- Result: Computing A_1 is NP-hard to approximate, #P-hard exactly
- Type: Computational complexity
- Gap knowledge: Shows it's hard to obtain
- Lower bounds: None on schedules themselves

## Gap in Literature

No paper proves:
1. Minimax lower bound: inf_u sup_Delta T(u, Delta) >= ...
2. Adversarial construction for gap-uninformed schedules
3. Separation ratio between informed and uninformed
4. Optimality of uniform slow for uninformed case

## Why the Gap Exists

Possible reasons:
1. Result considered obvious/folklore by experts
2. Community focuses on adaptive methods (where the gap is smaller)
3. Fixed uninformed schedules seen as uninteresting (who would use them?)
4. Proof technique is standard (adversarial argument), no new insights needed

## Conclusion

The Gap-Uninformed Separation Theorem appears NOVEL in formal statement. However:
- The argument is simple (may be folklore)
- The contribution is marginal (observation, not deep theorem)
- Expert validation recommended before claiming as contribution
