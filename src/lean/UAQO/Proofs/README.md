# UAQO Proofs Directory

This directory contains proofs that work toward eliminating axioms from the main UAQO formalization.

## Structure

```
Proofs/
    Foundations/           # Proofs for quantum mechanics foundations
        VariationalPrinciple.lean
    Spectral/              # Proofs for spectral analysis
        A2Bounds.lean
        ShermanMorrison.lean
    Adiabatic/             # Proofs for adiabatic evolution
        ScheduleProperties.lean
    Complexity/            # Proofs for complexity theory results
        SATSemantics.lean
        ModifiedHamDeg.lean
        BetaModifiedHam.lean
        LagrangeInterp.lean
    Mathlib/               # Bridge lemmas connecting to Mathlib
        FinsetArithmetic.lean
```

## Axiom Status

### Fully Proved (No Sorry) - 3 axioms

| Axiom | Source File | Proof File |
|-------|-------------|------------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | Complexity/SATSemantics.lean |
| `threeSATDegPositive_ground` | Hardness.lean | Complexity/SATSemantics.lean |
| `lagrange_interpolation` | SharpP.lean | Complexity/LagrangeInterp.lean |

### Partially Proved (With Sorry) - 13 axioms

| Axiom | Source File | Proof File | Notes |
|-------|-------------|------------|-------|
| `A2_lower_bound` | SpectralParameters.lean | Spectral/A2Bounds.lean | Bound direction needs verification |
| `modifiedHam_deg_sum` | Hardness.lean | Complexity/ModifiedHamDeg.lean | Needs Finset combinatorics |
| `modifiedHam_deg_count` | Hardness.lean | Complexity/ModifiedHamDeg.lean | Needs Finset combinatorics |
| `betaModifiedHam_deg_sum` | Hardness.lean | Complexity/BetaModifiedHam.lean | Needs Finset combinatorics |
| `betaModifiedHam_deg_count` | Hardness.lean | Complexity/BetaModifiedHam.lean | Needs Finset combinatorics |
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Complexity/BetaModifiedHam.lean | Case 2 needs universal gap constraint |
| `betaModifiedHam_eigenval_ordered_strict` | Hardness.lean | Complexity/BetaModifiedHam.lean | Case 2 needs universal gap constraint |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Complexity/BetaModifiedHam.lean | Upper bound needs E_k <= 1 - beta/2 |
| `variational_principle` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Needs Mathlib spectral theory |
| `variational_minimum` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Needs Mathlib spectral theory |
| `avoidedCrossing_bound` | Schedule.lean | Adiabatic/ScheduleProperties.lean | Real arithmetic |
| `piecewiseSchedule_monotone` | Schedule.lean | Adiabatic/ScheduleProperties.lean | Piecewise analysis |
| `shermanMorrison_resolvent` | GapBounds.lean | Spectral/ShermanMorrison.lean | Sign convention needs verification |

### External Foundations (Kept as Axioms) - 9 axioms

These require independent formalization projects:

| Axiom | Reason |
|-------|--------|
| `threeSAT_in_NP` | Cook-Levin theorem |
| `threeSAT_NP_complete` | Cook-Levin theorem |
| `sharpThreeSAT_in_SharpP` | Valiant's theorem |
| `sharpThreeSAT_complete` | Valiant's theorem |
| `sharpP_solves_NP` | Oracle complexity |
| `degeneracy_sharpP_hard` | Reduction proof |
| `adiabaticTheorem` | Quantum dynamics |
| `eigenpath_traversal` | Quantum dynamics |
| `resolvent_distance_to_spectrum` | Infinite-dim spectral theory |

### Not Yet Started - 20 axioms

Remaining axioms in GapBounds.lean, RunningTime.lean, and Hardness.lean:
- Gap bounds: `eigenvalue_condition`, `groundEnergy_variational_bound`, `firstExcited_lower_bound`
- Gap bounds (regional): `gap_bound_left_axiom`, `gap_at_avoided_crossing_axiom`, `gap_bound_right_axiom`
- Gap bounds (combined): `gap_bound_all_s_axiom`, `gap_minimum_at_crossing_axiom`
- Running time: `mainResult1`, `runningTime_ising_bound`, `lowerBound_unstructuredSearch`
- Running time: `runningTime_matches_lower_bound`, `measurement_yields_groundstate`
- Hardness: `A1_modification_formula`, `A1_polynomial_in_beta`
- Hardness: `mainResult2`, `A1_approx_implies_P_eq_NP`, `mainResult3`, `mainResult3_robust`
- Other: `threeSATWellFormed_numVars`

## Verification

```bash
cd /Users/arjo/Documents/base/uaqo/src/lean

# Build all proofs
lake build UAQO.Proofs.ProofVerify

# Count remaining axioms in main files
grep -rn "^axiom " UAQO/ | grep -v "Proofs/" | wc -l

# Check for sorries in proof files
grep -rn "sorry" UAQO/Proofs/ | grep -v README
```

## Approach

Each proof file:
1. Imports necessary modules from UAQO and Mathlib
2. Proves theorems that exactly match the axiom signatures
3. Uses `sorry` for incomplete parts that need more work

To eliminate an axiom completely:
1. Complete all `sorry` markers in the proof file
2. Replace the `axiom` declaration in the original file with an import
3. Add `theorem X := Proofs.X_proof` to re-export the result

## Summary

| Category | Count |
|----------|-------|
| Fully proved (no sorry) | 3 |
| Partially proved (with sorry) | 13 |
| External foundations (kept as axioms) | 9 |
| Not yet started | 20 |
| **Total axioms in main files** | **45** |
