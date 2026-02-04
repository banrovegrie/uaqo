# UAQO Proofs Directory

This directory contains proofs that eliminate axioms from the main UAQO formalization.

## Structure

```
Proofs/
    Foundations/           # Proofs for quantum mechanics foundations
    Spectral/              # Proofs for spectral analysis
    Adiabatic/             # Proofs for adiabatic evolution
    Complexity/            # Proofs for complexity theory results
    Mathlib/               # Bridge lemmas connecting to Mathlib
```

## Axiom Status

### Eliminated (Proved)

| Axiom | Source File | Proof File |
|-------|-------------|------------|
| `satisfies_iff_countUnsatisfied_zero` | Hardness.lean | Complexity/SATSemantics.lean |
| `threeSATDegPositive_ground` | Hardness.lean | Complexity/SATSemantics.lean |
| `threeSATWellFormed_numVars` | Hardness.lean | Complexity/SATSemantics.lean |
| `modifiedHam_deg_sum` | Hardness.lean | Complexity/ModifiedHamDeg.lean |
| `modifiedHam_deg_count` | Hardness.lean | Complexity/ModifiedHamDeg.lean |
| `betaModifiedHam_deg_sum` | Hardness.lean | Complexity/BetaModifiedHam.lean |
| `betaModifiedHam_deg_count` | Hardness.lean | Complexity/BetaModifiedHam.lean |
| `A2_lower_bound` | SpectralParameters.lean | Spectral/A2Bounds.lean |
| `avoidedCrossing_bound` | Schedule.lean | Adiabatic/ScheduleProperties.lean |
| `piecewiseSchedule_monotone` | Schedule.lean | Adiabatic/ScheduleProperties.lean |

### External Foundations (Kept as Axioms)

These require independent formalization projects:

- `threeSAT_in_NP`, `threeSAT_NP_complete` (Cook-Levin theorem)
- `sharpThreeSAT_in_SharpP`, `sharpThreeSAT_complete` (Valiant's theorem)
- `sharpP_solves_NP`, `degeneracy_sharpP_hard` (Oracle complexity)
- `adiabaticTheorem`, `eigenpath_traversal` (Quantum dynamics)
- `resolvent_distance_to_spectrum` (Infinite-dim spectral theory)

## Verification

```bash
cd /Users/arjo/Documents/base/uaqo/src/lean
lake build UAQO.Proofs
```

## Approach

Each proof file:
1. Imports necessary modules from UAQO and Mathlib
2. Proves theorems that exactly match the axiom signatures
3. Exports the proofs for use in the main files

The main files can then replace `axiom` with imports from the proof files.
