/-
  Gap-Uninformed Separation Theorem

  Formal verification of the theorem:

  For adiabatic quantum optimization with gap minimum at unknown s* in [s_L, s_R]:
    T_uninformed / T_informed >= (s_R - s_L) / delta_s

  For unstructured search with n qubits:
    T_uninformed / T_informed = Omega(2^{n/2})

  This quantifies the runtime cost of the NP-hardness of computing A_1.

  Reference: Extends "Unstructured Adiabatic Quantum Optimization: Optimality
  with Limitations" (Braida, Chakraborty, Chaudhuri, Cunningham, Menavlikar,
  Novo, Roland, 2025)

  Key insight: The proof is adversarial. For any fixed schedule, an adversary
  can place the gap minimum where the schedule is fastest, forcing high error.
  To achieve low error for ALL gap functions, the schedule must be slow
  everywhere in the uncertainty interval.
-/

import SeparationTheorem.Basic
import SeparationTheorem.Separation

namespace SeparationTheorem

/-! ## Main Results Summary -/

#check gap_uninformed_separation_theorem
#check separation_ratio
#check unstructured_search_separation
#check separation_exponential
#check velocity_bounded_everywhere
#check adversarialGap_in_class

/-! ## Verified Claims

1. **Adversarial Construction (Theorem `adversarialGap_in_class`)**:
   For any point s in [s_L, s_R], we can construct a gap function
   with minimum at s that belongs to the gap class.

2. **Velocity Bound (Theorem `velocity_bounded_everywhere`)**:
   Any schedule achieving error epsilon for all gaps in
   GapClass(s_L, s_R, Delta_star) must have velocity bounded by
   sqrt(epsilon) * Delta_star at every point in [s_L, s_R].

3. **Separation Ratio (Theorem `separation_ratio`)**:
   T_unf / T_inf = (s_R - s_L) * sqrt(epsilon)
   For constant epsilon, this is Theta((s_R - s_L) / Delta_star).

4. **Unstructured Search (Theorem `unstructured_search_separation`)**:
   For n-qubit unstructured search with Delta_star = 2^{-n/2}
   and constant uncertainty interval width, the separation is Omega(2^{n/2}).

5. **Main Theorem (Theorem `gap_uninformed_separation_theorem`)**:
   Combines all the above into a single statement.
-/

end SeparationTheorem
