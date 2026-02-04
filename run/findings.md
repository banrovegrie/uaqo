# Findings: Thesis Implementation

## Source Material Overview

### Paper (arXiv:2411.05736)
Primary source for all technical content in Chapters 5-8.
- Section 2: Spectral analysis, gap bounds
- Section 3: Optimal schedule construction (Alapan's contribution)
- Section 4: Hardness results (NP-hard, #P-hard)

### Experiments (Thesis Extensions for Chapter 9)

| Experiment | Topic | Section |
|------------|-------|---------|
| 02_robust_schedules | Hedging with bounded uncertainty | 9.2 |
| 04_separation_theorem | Gap-uninformed schedules lower bound | 9.1 |
| 05_adaptive_schedules | Binary search with phase estimation | 9.4 |
| 06_measure_condition | Gap geometry, flatness parameter | 9.5 |
| 07_partial_information | Interpolation theorem | 9.3 |

### Lean Formalization
Located at src/lean/UAQO/. Key modules:
- Foundations/ - Quantum mechanics basics
- Spectral/ - Gap analysis
- Adiabatic/ - Evolution and schedules
- Complexity/ - Hardness proofs
- Proofs/ - Axiom eliminations

See src/lean/UAQO/Proofs/README.md for axiom status.

## Style Guidelines (from taste/README.md)

Key principles:
1. Every sentence carries information
2. Definitions motivated before stated
3. Explicit bounds and conditions on all theorems
4. Honest about limitations
5. No filler, no scaffolding phrases

## Notation Consistency

Import math directly from paper where possible.
Use src/tests/check-math.md as reference.

Common terms (do not re-define across chapters):
- Hermitian, unitary
- Spectral gap
- Ground state, eigenstate

## Chapter Dependencies

```
Ch 2 (Physics) --> Ch 3 (Quantum) --> Ch 4 (AQC)
                                          |
                                          v
                   Ch 5 (AQO) --> Ch 6 (Spectral) --> Ch 7 (Schedule)
                                                          |
                                                          v
                                                     Ch 8 (Hardness)
                                                          |
                                                          v
                                                     Ch 9 (Extensions)
```

Ch 1 (Introduction) and Ch 10 (Conclusion) written last.
