/-
  Gap-Uninformed Separation Theorem: Error Bounds

  This file axiomatizes the Jansen-Ruskai-Seiler error bounds for adiabatic evolution.
  These are established results from the literature (2007) that we take as given.

  Key bound: error ~ (1/T) * integral of (velocity^2 / gap^3)
-/
import SeparationTheorem.GapClass

namespace SeparationTheorem

/-! ## Jansen-Ruskai-Seiler Error Bound (Axiomatized) -/

/-- The adiabatic error bound from Jansen-Ruskai-Seiler 2007.
    The error is bounded by:
      eta(s) <= (C/T) * { boundary terms + integral_0^s (|u''|/Delta^2 + |u'|^2/Delta^3) ds }

    We axiomatize this as a function of schedule and gap. -/
axiom adiabaticErrorBound (sched : Schedule) (gap : GapFunction) (T : Real) (hT : T > 0) :
    Real

/-- The error bound is dominated by the velocity-gap interaction term -/
axiom errorBound_velocity_dominated (sched : Schedule) (gap : GapFunction)
    (T : Real) (hT : T > 0) :
    adiabaticErrorBound sched gap T hT ≤
      (1 / T) * ∫ s in Set.Icc 0 1, (sched.velocity s)^2 / (gap.Delta s)^3

/-- The error bound increases with velocity at the gap minimum -/
axiom errorBound_velocity_at_minimum (sched : Schedule) (gap : GapFunction)
    (T : Real) (hT : T > 0) :
    let s_star := gap.minPosition
    let v_star := sched.velocity s_star
    let Delta_star := gap.minGap
    adiabaticErrorBound sched gap T hT ≥
      (1 / T) * v_star^2 * (crossingWidth Delta_star) / Delta_star^3

/-! ## Guo-An Optimal Schedule (Axiomatized) -/

/-- The optimal gap-informed schedule has velocity proportional to gap^(3/2) -/
def isOptimalInformed (sched : Schedule) (gap : GapFunction) : Prop :=
  ∀ s ∈ Set.Icc 0 1, ∃ c > 0, sched.velocity s = c * (gap.Delta s) ^ (3/2 : Real)

/-- For the optimal informed schedule, evolution time is O(1/Delta_*) -/
axiom optimalInformed_time (gap : GapFunction) (epsilon : Real) (heps : epsilon > 0) :
    ∃ sched : Schedule, isOptimalInformed sched gap ∧
      evolutionTime sched gap epsilon ≤ (1 / epsilon) * (1 / gap.minGap)

/-! ## Time Required for Constant Error -/

/-- Time required for epsilon-error with a given schedule -/
noncomputable def timeForError (sched : Schedule) (gap : GapFunction)
    (epsilon : Real) (heps : epsilon > 0) : Real :=
  sInf { T : Real | T > 0 ∧ adiabaticErrorBound sched gap T (by linarith) ≤ epsilon }

/-- The gap-informed time is O(1/Delta_*) -/
theorem informed_time_bound (gap : GapFunction) (epsilon : Real) (heps : epsilon > 0) :
    ∃ sched : Schedule, ∃ C > 0,
      timeForError sched gap epsilon heps ≤ C / gap.minGap := by
  sorry

end SeparationTheorem
