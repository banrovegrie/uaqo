import CircumventingBarrier.Basic
import CircumventingBarrier.NoGo
import CircumventingBarrier.RankKMultilevelCommuting
import Std

namespace CircumventingBarrier

/-- Abstract product-sector model for Theorem 1 operator core. -/
structure ProductSectorModel (Sys Anc : Type) where
  phi : Anc
  Hbare : Rat -> Sys -> Sys
  Hext : Rat -> Prod Sys Anc -> Prod Sys Anc
  onSector : forall s : Rat, forall psi : Sys,
    Hext s (Prod.mk psi phi) = Prod.mk (Hbare s psi) phi

/-- States in the product sector `Prod Sys {phi}`. -/
def inProductSector {Sys Anc : Type} (m : ProductSectorModel Sys Anc)
    (state : Prod Sys Anc) : Prop :=
  state.2 = m.phi

/-- One-step invariance of the product sector under the extended operator. -/
theorem sector_invariant_one_step {Sys Anc : Type} (m : ProductSectorModel Sys Anc)
    (s : Rat) (state : Prod Sys Anc)
    (hState : inProductSector m state) :
    inProductSector m (m.Hext s state) := by
  cases state with
  | mk psi a =>
      dsimp [inProductSector] at hState
      dsimp [inProductSector]
      subst a
      simpa using congrArg Prod.snd (m.onSector s psi)

/-- n-step evolution map for a fixed schedule value `s`. -/
def evolveNTimes {Sys Anc : Type} (m : ProductSectorModel Sys Anc)
    (s : Rat) : Nat -> Prod Sys Anc -> Prod Sys Anc
  | 0, state => state
  | Nat.succ n, state => evolveNTimes m s n (m.Hext s state)

/-- Product-sector invariance for all finite evolution depths. -/
theorem sector_invariant_n_steps {Sys Anc : Type} (m : ProductSectorModel Sys Anc)
    (s : Rat) (n : Nat) (state : Prod Sys Anc)
    (hState : inProductSector m state) :
    inProductSector m (evolveNTimes m s n state) := by
  induction n with
  | zero =>
      simpa [evolveNTimes] using hState
  | succ n ih =>
      simp [evolveNTimes]
      exact ih (sector_invariant_one_step m s state hState)

/-- Reduced action on the product sector. -/
def reducedAction {Sys Anc : Type} (m : ProductSectorModel Sys Anc) : Rat -> Sys -> Sys :=
  fun s psi => (m.Hext s (psi, m.phi)).1

/-- The reduced action equals the bare action exactly. -/
theorem reducedAction_eq_bare {Sys Anc : Type} (m : ProductSectorModel Sys Anc) :
    reducedAction m = m.Hbare := by
  funext s
  funext psi
  exact congrArg Prod.fst (m.onSector s psi)

/--
Theorem 1 operator-core transfer:
for any crossing functional on operator families, the reduced extended-sector
crossing equals the bare crossing because the actions are equal.
-/
theorem theorem1_crossing_functional_invariant {Sys Anc : Type}
    (m : ProductSectorModel Sys Anc)
    (cross : (Rat -> Sys -> Sys) -> Rat) :
    cross (reducedAction m) = cross m.Hbare := by
  exact congrArg cross (reducedAction_eq_bare m)

/-- Coupled asymptotic profile used in Theorem 3 core reduction. -/
def coupledAeff (C K Delta : Rat) : Rat :=
  C + K / Delta

/-- Crossing map induced by the coupled asymptotic profile. -/
def coupledCrossing (C K Delta : Rat) : Rat :=
  crossingPosition (coupledAeff C K Delta)

/--
Theorem 3 core reduction:
if `A_1^eff(Delta) = C + K/Delta` with `K > 0`, then crossing is non-constant
in `Delta` over positive gaps.
-/
theorem theorem3_asymptotic_nonconstant (C K Delta1 Delta2 : Rat)
    (hC : 0 <= C) (hK : 0 < K)
    (hDelta1 : 0 < Delta1) (hDelta2 : 0 < Delta2)
    (hNe : Delta1 != Delta2) :
    coupledCrossing C K Delta1 != coupledCrossing C K Delta2 := by
  simpa [coupledCrossing, coupledAeff]
    using commutingBranch_nonconstant_in_Delta C K Delta1 Delta2
      hC hK hDelta1 hDelta2 hNe

/-- Segment-2 crossing map from Theorem 4. -/
def segment2Crossing (B1 : Rat) : Rat :=
  crossingPosition B1

/-- Theorem 4 core rigidity map: if `B1 = A1`, the segment-2 crossing matches base crossing. -/
theorem theorem4_rigidity_map (A1 B1 : Rat) (hEq : B1 = A1) :
    segment2Crossing B1 = crossingPosition A1 := by
  simp [segment2Crossing, hEq]

end CircumventingBarrier
