# Experiments Summary

## Current Focus: Gap-Uninformed Separation Theorem

**Goal**: Prove that schedules not knowing the gap position require Ω(2^{n/2}) more time than informed schedules.

**Status**: THEOREM PROVEN. Formal proof complete, novelty verified against 7 papers.

**Location**: `04_separation_theorem/`


## Folder Structure

```
experiments/
├── TODO.md              # Active tasks
├── SUMMARY.md           # This file
├── README.md            # (Frozen) Original README
│
├── 01_precision_gap/    # Complexity at intermediate precision
├── 02_robust_schedules/ # Numerical experiments on robust schedules
├── 03_structured_tractability/ # When is A_1 tractable?
├── 04_separation_theorem/      # MAIN THEORETICAL WORK
│   └── main_theorem.md  # Theorem statement and proof
│
└── archive/             # Previous explorations
```


## Novelty Verification

| Existing Work | Their Contribution | What's Missing |
|--------------|-------------------|----------------|
| Original paper | A_1 is NP-hard | Runtime cost not quantified |
| Guo-An 2025 | Optimal when informed | Uninformed case not addressed |
| Matsuura 2021 | Variational method | No separation bounds |
| Shingu-Hatomura 2025 | Geometrical method | No optimality proof |

**Our contribution**: Prove minimax optimality and separation bounds for gap-uninformed schedules.


## Key References

1. Jansen-Ruskai-Seiler (2007) - Adiabatic error bounds
2. Guo-An (2025) - Variational optimality framework
3. Original paper - A_1 NP-hardness


## Next Steps

The main theorem is proven. Remaining work:
1. Make constants explicit
2. Extend to partial information
3. Consider Lean formalization (long-term)

See `TODO.md` for detailed task list.
