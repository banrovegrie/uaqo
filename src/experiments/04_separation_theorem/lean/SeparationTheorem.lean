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

#check separation_ratio
#check separation_ratio_simplified
#check unstructured_search_separation
#check separation_exponential

/-! ## Verified Claims

1. **Lower Bound (Theorem `uninformed_time_lower_bound`)**:
   Any fixed schedule achieving error epsilon for all gaps in
   GapClass(s_L, s_R, Delta_star) requires time at least
   (s_R - s_L) / (sqrt(epsilon) * Delta_star).

2. **Upper Bound (Theorem `informed_time_upper_bound`)**:
   An informed schedule knowing the gap achieves time 1/(epsilon * Delta_star).

3. **Separation (Theorem `separation_ratio`)**:
   The ratio T_unf / T_inf = (s_R - s_L) * sqrt(epsilon) / 1
   For constant epsilon, this is Theta((s_R - s_L) / Delta_star).

4. **Unstructured Search (Theorem `unstructured_search_separation`)**:
   For n-qubit unstructured search with Delta_star = 2^{-n/2}
   and constant uncertainty interval width, the separation is Omega(2^{n/2}).
-/

end SeparationTheorem
