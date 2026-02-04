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

## Fully Proved (7 axioms, 0 sorry)
- `satisfies_iff_countUnsatisfied_zero` (SATSemantics.lean)
- `threeSATDegPositive_ground` (SATSemantics.lean)
- `lagrange_interpolation` (LagrangeInterp.lean)
- `betaModifiedHam_deg_sum` (BetaModifiedHam.lean)
- `betaModifiedHam_deg_count` (BetaModifiedHam.lean)
- `modifiedHam_deg_sum` (Hardness.lean - now a theorem)
- `modifiedHam_deg_count` (ModifiedHamDeg.lean - full proof)

Note: modifiedHam_deg_sum/count were fixed by removing level M from the construction.
The modified Hamiltonian now keeps M levels with doubled degeneracies.

## Axioms with Formulation Issues (3 axioms)
These appear to have bugs - see README.md for details:
- `A2_lower_bound` (A2Bounds.lean) - bound direction reversed
- `avoidedCrossing_bound`, `piecewiseSchedule_monotone` (ScheduleProperties.lean) - missing hypothesis

## Partially Proved with Sorry (6 axioms)
Need additional hypotheses or Mathlib dependencies:
- `betaModifiedHam_eigenval_ordered`, `betaModifiedHam_eigenval_ordered_strict` (BetaModifiedHam.lean)
- `betaModifiedHam_eigenval_bounds` (BetaModifiedHam.lean)
- `variational_principle`, `variational_minimum` (VariationalPrinciple.lean)
- `shermanMorrison_resolvent` (ShermanMorrison.lean)

## External Foundations (9 axioms - kept as axioms)
- `threeSAT_in_NP`, `threeSAT_NP_complete` (Cook-Levin)
- `sharpThreeSAT_in_SharpP`, `sharpThreeSAT_complete` (Valiant)
- `sharpP_solves_NP`, `degeneracy_sharpP_hard` (Oracle complexity)
- `adiabaticTheorem`, `eigenpath_traversal` (Quantum dynamics)
- `resolvent_distance_to_spectrum` (Spectral theory)

## Not Yet Started (~18 axioms)
Remaining axioms in GapBounds.lean, RunningTime.lean, and Hardness.lean.
-/

end UAQO.Proofs
