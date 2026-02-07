import CircumventingBarrier.Basic
import CircumventingBarrier.Universality
import Std

namespace CircumventingBarrier

/-- Uncoupled crossing map remains A_1-dependent on physical domain A_1 > 0. -/
def uncoupledDependsOnA1 : Prop :=
  forall a b : Rat, 0 < a -> 0 < b -> a != b -> crossingPosition a != crossingPosition b

/-- Product ancilla model map (core abstraction of Theorem 1). -/
def productAncillaCrossing (a1 : Rat) : Rat :=
  crossingPosition a1

/-- Coupled fixed-shift model map (core abstraction of Theorem 3). -/
def coupledShiftCrossing (shift a1 : Rat) : Rat :=
  crossingPosition (a1 + shift)

/-- Multi-segment final crossing map (core abstraction of Theorem 4). -/
def multisegmentCrossing (b1 : Rat) : Rat :=
  crossingPosition b1

/-- Theorem 1 core statement: product ancilla leaves crossing map unchanged. -/
def theorem1_statement : Prop :=
  forall a1 : Rat, productAncillaCrossing a1 = crossingPosition a1

/-- Theorem 2 statement (imported from Universality.lean). -/
def theorem2_statement : Prop :=
  theorem2_universality_statement

/-- Theorem 3 core statement: fixed shift does not collapse dependence in A_1. -/
def theorem3_statement : Prop :=
  forall shift : Rat, 0 <= shift ->
    forall a b : Rat, 0 < a -> 0 < b -> a != b ->
      coupledShiftCrossing shift a != coupledShiftCrossing shift b

/-- Theorem 4 core statement: if B_1 = A_1, final crossing equals base crossing. -/
def theorem4_statement : Prop :=
  forall a1 b1 : Rat, b1 = a1 -> multisegmentCrossing b1 = crossingPosition a1

/-- Theorem 5 no-go statement (core): component statements 1-4 are packaged with
the uncoupled/coupled nonconstancy conclusions. -/
def theorem5_statement : Prop :=
  And theorem1_statement (And theorem2_statement
    (And uncoupledDependsOnA1 (And theorem3_statement theorem4_statement)))

/-- Injectivity of A_1/(A_1+1) on A_1 > 0. -/
theorem crossingPosition_injective_pos : uncoupledDependsOnA1 := by
  intro a b ha hb hab hEq
  have hapos : 0 < a + 1 := add_pos_of_pos_of_nonneg ha (by decide)
  have hbpos : 0 < b + 1 := add_pos_of_pos_of_nonneg hb (by decide)
  have hdenA : a + 1 != 0 := ne_of_gt hapos
  have hdenB : b + 1 != 0 := ne_of_gt hbpos
  have hCross : a * (b + 1) = b * (a + 1) := by
    exact (div_eq_div_iff hdenA hdenB).1 hEq
  have hExpanded : a * b + a = b * a + b := by
    simpa [mul_add, add_mul] using hCross
  have hCancel : a * b + a = a * b + b := by
    simpa [mul_comm] using hExpanded
  have hAB : a = b := add_left_cancel hCancel
  exact hab hAB

/-- Product ancilla invariance (core). -/
theorem theorem1_holds : theorem1_statement := by
  intro a1
  rfl

/-- Fixed-shift coupled map remains nonconstant in A_1 (core). -/
theorem theorem3_holds : theorem3_statement := by
  intro shift hshift a b ha hb hab
  have hsa : 0 < a + shift := add_pos_of_pos_of_nonneg ha hshift
  have hsb : 0 < b + shift := add_pos_of_pos_of_nonneg hb hshift
  have hneShifted : a + shift != b + shift := by
    intro hEq
    have hEqAB : a = b := by linarith
    exact hab hEqAB
  exact crossingPosition_injective_pos (a + shift) (b + shift) hsa hsb hneShifted

/-- Multi-segment rigidity implication (core). -/
theorem theorem4_holds : theorem4_statement := by
  intro a1 b1 hEq
  simp [multisegmentCrossing, hEq]

/-- Composition theorem: Theorems 1-4 imply Theorem 5 (core composition). -/
theorem theorem5_from_components
    (h1 : theorem1_statement)
    (h2 : theorem2_statement)
    (h3 : theorem3_statement)
    (h4 : theorem4_statement) :
    theorem5_statement := by
  exact And.intro h1 (And.intro h2 (And.intro crossingPosition_injective_pos (And.intro h3 h4)))

/-- Theorem 5 obtained from proved component cores. -/
theorem theorem5_holds : theorem5_statement := by
  exact theorem5_from_components theorem1_holds theorem2_universality_holds theorem3_holds theorem4_holds

end CircumventingBarrier
