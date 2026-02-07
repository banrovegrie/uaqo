import Std

namespace CircumventingBarrier

/-- Spectral data for an unstructured instance. -/
structure SpectralData where
  numStates : Nat
  numLevels : Nat
  energies : Fin numLevels -> Rat
  degeneracies : Fin numLevels -> Nat

/-- Weight used in the rank-one secular equation: w_k = d_k / N. -/
def weightFromDegeneracy (sd : SpectralData) (k : Fin sd.numLevels) : Rat :=
  (sd.degeneracies k : Rat) / (sd.numStates : Rat)

/-- Crossing map s*(A_1) = A_1 / (A_1 + 1). -/
def crossingPosition (a1 : Rat) : Rat :=
  a1 / (a1 + 1)

/-- Effective first spectral parameter for abstract weights and inverse gaps. -/
def effectiveA1 {M : Nat} (weights inverseGaps : Fin M -> Rat) : Rat :=
  Finset.univ.sum (fun k => weights k * inverseGaps k)

/-- Spectrum-independence of a crossing map. -/
def isSpectrumIndependent (f : Rat -> Rat) : Prop :=
  forall a b : Rat, f a = f b

end CircumventingBarrier
