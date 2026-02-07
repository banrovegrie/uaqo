import CircumventingBarrier.Basic
import Std

namespace CircumventingBarrier

/-- Probability mass function on computational basis states. -/
abbrev Probability (N : Nat) := Fin N -> Rat

/-- A level assignment labels each basis state by an energy level index. -/
abbrev Assignment (N M : Nat) := Fin N -> Fin M

/-- Normalization condition for a probability distribution. -/
def normalized {N : Nat} (p : Probability N) : Prop :=
  Finset.univ.sum (fun z => p z) = 1

/-- Nonnegativity condition for a probability distribution. -/
def nonnegative {N : Nat} (p : Probability N) : Prop :=
  forall z : Fin N, 0 <= p z

/-- Weight of level k for assignment sigma and distribution p. -/
def levelWeight {N M : Nat} (p : Probability N) (sigma : Assignment N M)
    (k : Fin M) : Rat :=
  Finset.univ.sum (fun z => if sigma z = k then p z else 0)

/-- Uniform overlaps in computational basis. -/
def uniformDistribution {N : Nat} (p : Probability N) : Prop :=
  forall z : Fin N, p z = (1 : Rat) / (N : Rat)

/-- Two-level assignment that singles out one basis state as level 0. -/
def singledOutAssignment {N : Nat} (target : Fin N) : Assignment N 2 :=
  fun z => if z = target then (0 : Fin 2) else (1 : Fin 2)

/-- Invariance under all singleton-vs-rest assignments (degeneracy pattern 1 and N-1). -/
def singletonInvariant {N : Nat} (p : Probability N) : Prop :=
  forall i j : Fin N,
    levelWeight p (singledOutAssignment i) (0 : Fin 2) =
    levelWeight p (singledOutAssignment j) (0 : Fin 2)

/-- For a singled-out assignment, level-0 weight equals the singled-out probability. -/
theorem levelWeight_singledOut_ground {N : Nat} (p : Probability N) (target : Fin N) :
    levelWeight p (singledOutAssignment target) (0 : Fin 2) = p target := by
  classical
  simp [levelWeight, singledOutAssignment]

/-- Singleton invariance forces pairwise equality of basis probabilities. -/
theorem singletonInvariant_pairwise_eq {N : Nat} (p : Probability N)
    (hInv : singletonInvariant p) (i j : Fin N) :
    p i = p j := by
  have hEqWeights := hInv i j
  simpa [levelWeight_singledOut_ground] using hEqWeights

/-- Uniform distribution implies singleton-assignment invariance. -/
theorem singletonInvariant_of_uniform {N : Nat} (p : Probability N)
    (hUni : uniformDistribution p) :
    singletonInvariant p := by
  intro i j
  simp [levelWeight_singledOut_ground, hUni]

/--
Theorem 2 core (formalized):
if singleton-vs-rest weights are assignment-invariant and probabilities are normalized,
then all basis probabilities are uniform.
-/
theorem uniform_from_singletonInvariant {N : Nat} (hN : 0 < N)
    (p : Probability N)
    (hNorm : normalized p)
    (_hNonneg : nonnegative p)
    (hInv : singletonInvariant p) :
    uniformDistribution p := by
  let z0 : Fin N := Fin.mk 0 hN

  have hPair : forall z : Fin N, p z = p z0 := by
    intro z
    exact singletonInvariant_pairwise_eq p hInv z z0

  have hSumConst : Finset.univ.sum (fun z : Fin N => p z) = (N : Rat) * p z0 := by
    calc
      Finset.univ.sum (fun z : Fin N => p z)
          = Finset.univ.sum (fun _ : Fin N => p z0) := by
              apply Finset.sum_congr rfl
              intro z _
              exact hPair z
      _ = (Finset.univ.card : Rat) * p z0 := by
            simp
      _ = (N : Rat) * p z0 := by
            simp

  have hMul : (N : Rat) * p z0 = 1 := by
    simpa [hSumConst] using hNorm

  have hN_ne : (N : Rat) != 0 := by
    exact_mod_cast (Nat.ne_of_gt hN)

  have hz0 : p z0 = (1 : Rat) / (N : Rat) := by
    apply (div_eq_iff hN_ne).2
    simpa [mul_comm] using hMul

  intro z
  calc
    p z = p z0 := hPair z
    _ = (1 : Rat) / (N : Rat) := hz0

/--
Theorem 2 statement encoding used in this package.
This is the permutation argument core specialized to the d0=1 two-level family.
-/
def theorem2_universality_statement : Prop :=
  forall (N : Nat),
    1 < N ->
    forall p : Probability N,
      normalized p ->
      nonnegative p ->
      singletonInvariant p ->
      uniformDistribution p

theorem theorem2_universality_holds : theorem2_universality_statement := by
  intro N hN p hNorm hNonneg hInv
  have hNpos : 0 < N := lt_trans (by decide : 0 < 1) hN
  exact uniform_from_singletonInvariant hNpos p hNorm hNonneg hInv

/--
Bidirectional characterization of the theorem-2 core under normalization:
singleton-invariance is equivalent to uniform overlaps.
-/
theorem singletonInvariant_iff_uniform {N : Nat} (hN : 0 < N)
    (p : Probability N)
    (hNorm : normalized p)
    (hNonneg : nonnegative p) :
    singletonInvariant p <-> uniformDistribution p := by
  constructor
  . intro hInv
    exact uniform_from_singletonInvariant hN p hNorm hNonneg hInv
  . intro hUni
    exact singletonInvariant_of_uniform p hUni

end CircumventingBarrier
