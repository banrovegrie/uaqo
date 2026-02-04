/-
  Common Finset lemmas needed across multiple proofs.

  These bridge lemmas connect UAQO definitions to Mathlib's Finset API.
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace UAQO.Proofs.Mathlib

/-- Cardinality of disjoint union equals sum of cardinalities. -/
lemma card_biUnion_disjoint {α β : Type*} [DecidableEq α] [DecidableEq β]
    {s : Finset β} {f : β → Finset α}
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (f i) (f j)) :
    (Finset.biUnion s f).card = Finset.sum s (fun i => (f i).card) := by
  exact Finset.card_biUnion hdisj

/-- Finset.sum respects equality of functions. -/
lemma sum_congr_fun {α β : Type*} [AddCommMonoid β]
    (s : Finset α) (f g : α → β) (h : ∀ a ∈ s, f a = g a) :
    Finset.sum s f = Finset.sum s g :=
  Finset.sum_congr rfl h

end UAQO.Proofs.Mathlib
