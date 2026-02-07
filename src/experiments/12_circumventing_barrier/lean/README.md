# Lean Formalization: Experiment 12

## Scope

This local Lean package encodes statement-level formalization targets for Experiment 12:

1. Basic spectral definitions (weights, crossing map)
2. Theorem 2 core (universality via singleton-assignment permutation argument)
3. Theorem 5 core composition statement (Theorems 1-4 core abstractions imply no-go)
4. Proposition 6 algebraic core (rank-2 reduced scaling normal form)
5. Proposition 6A algebraic core (rank-k two-level branch scaling and non-constancy)
6. Proposition 6B algebraic core (commuting multilevel single-gap non-constancy)
7. Proposition 6C algebraic core (trace-drift root-multiset no-go form)
8. Theorems 1/3/4 operator-reduction cores (product-sector invariance, coupled asymptotic nonconstancy, segment rigidity map)

Files:
- `CircumventingBarrier/Basic.lean`
- `CircumventingBarrier/Universality.lean`
- `CircumventingBarrier/NoGo.lean`
- `CircumventingBarrier/Rank2TwoLevel.lean`
- `CircumventingBarrier/RankKTwoLevel.lean`
- `CircumventingBarrier/RankKMultilevelCommuting.lean`
- `CircumventingBarrier/RankKMultilevelTraceNoGo.lean`
- `CircumventingBarrier/OperatorCore134.lean`
- `CircumventingBarrier.lean`

## Build

From this directory:

```bash
lake build
```

## What Is Proved vs Axiomatized

Proved in Lean:
- `crossingPosition_injective_pos` in `NoGo.lean`
  - injectivity of `a/(a+1)` on the physical regime `a > 0`
- `theorem2_universality_holds` in `Universality.lean`
  - theorem-2 core via singleton-assignment permutation argument
- `singletonInvariant_iff_uniform` in `Universality.lean`
  - bidirectional core characterization (normalized regime)
- `theorem5_from_components` (composition theorem)
- `theorem5_holds` (composition instantiated from proved component cores)
- `reducedBranch_rewrite_A1` and `reducedBranch_nonconstant_in_Delta` in `RankKTwoLevel.lean`
  - algebraic core identity and non-constancy used in Proposition 6A
- `rank2ReducedEq_iff_normalized`, `rank2_root_has_linear_scaling`, and
  `rank2_root_from_normalized` in `Rank2TwoLevel.lean`
  - algebraic scaling core used in Proposition 6
- `commutingBranch_nonconstant_in_Delta` and
  `multilevel_branch_nonconstant_component` in `RankKMultilevelCommuting.lean`
  - algebraic commuting-multilevel non-constancy core used in Proposition 6B
- `reciprocalRootSum_perm` and `multilevel_trace_nogo_list_form` in
  `RankKMultilevelTraceNoGo.lean`
  - algebraic trace-drift contradiction core used in Proposition 6C
- `theorem1_crossing_functional_invariant`, `theorem3_asymptotic_nonconstant`,
  and `theorem4_rigidity_map` in `OperatorCore134.lean`
  - operator-reduction cores for Theorems 1, 3, and 4

Axiomatized:
- None in this experiment-local package.

## Notes

This package is intentionally self-contained and local to Experiment 12.
It does not modify `src/lean/` global thesis formalization.
Theorems 1/3/4 are encoded as explicit core abstractions in `NoGo.lean`.
