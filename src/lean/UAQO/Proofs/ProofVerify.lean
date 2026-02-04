/-
  Verification file for all proofs.

  Imports all proof modules to verify they compile correctly.
-/

-- Mathlib bridges
import UAQO.Proofs.Mathlib.FinsetArithmetic

-- Foundations proofs
import UAQO.Proofs.Foundations.VariationalPrinciple

-- Spectral proofs
import UAQO.Proofs.Spectral.A2Bounds
import UAQO.Proofs.Spectral.ShermanMorrison

-- Adiabatic proofs
import UAQO.Proofs.Adiabatic.ScheduleProperties

-- Complexity proofs
import UAQO.Proofs.Complexity.SATSemantics
import UAQO.Proofs.Complexity.ModifiedHamDeg
import UAQO.Proofs.Complexity.BetaModifiedHam
import UAQO.Proofs.Complexity.LagrangeInterp

namespace UAQO.Proofs

/-!
# Axiom Elimination Status

## Fully Proved (2 axioms, 0 sorry)
- `satisfies_iff_countUnsatisfied_zero` (SATSemantics.lean)
- `threeSATDegPositive_ground` (SATSemantics.lean)

## Partially Proved with Sorry (14 axioms)
These have proof structures in place but need completion:
- `A2_lower_bound` (A2Bounds.lean)
- `modifiedHam_deg_sum`, `modifiedHam_deg_count` (ModifiedHamDeg.lean)
- `betaModifiedHam_deg_sum`, `betaModifiedHam_deg_count` (BetaModifiedHam.lean)
- `betaModifiedHam_eigenval_ordered`, `betaModifiedHam_eigenval_ordered_strict` (BetaModifiedHam.lean)
- `betaModifiedHam_eigenval_bounds` (BetaModifiedHam.lean)
- `variational_principle`, `variational_minimum` (VariationalPrinciple.lean)
- `avoidedCrossing_bound`, `piecewiseSchedule_monotone` (ScheduleProperties.lean)
- `shermanMorrison_resolvent` (ShermanMorrison.lean)
- `lagrange_interpolation` (LagrangeInterp.lean)

## External Foundations (9 axioms - kept as axioms)
- `threeSAT_in_NP`, `threeSAT_NP_complete` (Cook-Levin)
- `sharpThreeSAT_in_SharpP`, `sharpThreeSAT_complete` (Valiant)
- `sharpP_solves_NP`, `degeneracy_sharpP_hard` (Oracle complexity)
- `adiabaticTheorem`, `eigenpath_traversal` (Quantum dynamics)
- `resolvent_distance_to_spectrum` (Spectral theory)

## Not Yet Started (~20 axioms)
Remaining axioms in GapBounds.lean, RunningTime.lean, and Hardness.lean
that need proof files created.
-/

end UAQO.Proofs
