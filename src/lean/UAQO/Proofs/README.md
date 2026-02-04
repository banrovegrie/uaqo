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

### Fully Proved (No Sorry)

| Axiom | Source File | Proof File |
|-------|-------------|------------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | Complexity/SATSemantics.lean |
| `threeSATDegPositive_ground` | Hardness.lean | Complexity/SATSemantics.lean |

### Partially Proved (With Sorry)

| Axiom | Source File | Proof File | Notes |
|-------|-------------|------------|-------|
| `A2_lower_bound` | SpectralParameters.lean | Spectral/A2Bounds.lean | Structure complete |
| `modifiedHam_deg_sum` | Hardness.lean | Complexity/ModifiedHamDeg.lean | Needs Finset combinatorics |
| `modifiedHam_deg_count` | Hardness.lean | Complexity/ModifiedHamDeg.lean | Needs Finset combinatorics |
| `betaModifiedHam_deg_sum` | Hardness.lean | Complexity/BetaModifiedHam.lean | Needs Finset combinatorics |
| `betaModifiedHam_deg_count` | Hardness.lean | Complexity/BetaModifiedHam.lean | Needs Finset combinatorics |
| `betaModifiedHam_eigenval_ordered` | Hardness.lean | Complexity/BetaModifiedHam.lean | Case analysis needed |
| `betaModifiedHam_eigenval_ordered_strict` | Hardness.lean | Complexity/BetaModifiedHam.lean | Needs gap constraint |
| `betaModifiedHam_eigenval_bounds` | Hardness.lean | Complexity/BetaModifiedHam.lean | Real arithmetic |
| `variational_principle` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Spectral decomposition |
| `variational_minimum` | SpectralTheory.lean | Foundations/VariationalPrinciple.lean | Spectral decomposition |
| `avoidedCrossing_bound` | Schedule.lean | Adiabatic/ScheduleProperties.lean | Real arithmetic |
| `piecewiseSchedule_monotone` | Schedule.lean | Adiabatic/ScheduleProperties.lean | Piecewise analysis |
| `shermanMorrison_resolvent` | GapBounds.lean | Spectral/ShermanMorrison.lean | Matrix identity |
| `lagrange_interpolation` | SharpP.lean | Complexity/LagrangeInterp.lean | Mathlib Polynomial.interpolate |

### External Foundations (Kept as Axioms)

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
