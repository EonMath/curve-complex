import CurveComplexGenusTwo.Topology.WeightedSurgery.WeightedSurgeryEvent

namespace CurveComplex.WeightedFlowScratch

variable {V B B' : Type*} [DecidableEq V] [DecidableEq B] [DecidableEq B']

theorem branchingSurgeryPoint_equiv_branches (K : AbstractSimplicialComplex V)
    (σ : Finset V) (hσ : σ ∈ K.faces) (selected : σ)
    (β : Finset B) (hne : β.Nonempty) (f : B → V)
    (hτ : σ ∪ β.image f ∈ K.faces)
    (β' : Finset B') (hne' : β'.Nonempty) (f' : B' → V)
    (hτ' : σ ∪ β'.image f' ∈ K.faces)
    (e : B ≃ B') (hβ : β.image e = β') (hf : ∀ b, f' (e b) = f b)
    (z : EdgeTime × FiniteSimplex σ) :
    branchingSurgeryPoint K σ hσ selected β hne f hτ z =
      branchingSurgeryPoint K σ hσ selected β' hne' f' hτ' z := by
  have hcard : β.card = β'.card := by
    rw [← hβ]
    exact (Finset.card_image_of_injective _ e.injective).symm
  have hsum (v : V) :
      (∑ b ∈ β, if f b = v then surgeryCutMass σ selected z else 0) =
      ∑ b ∈ β', if f' b = v then surgeryCutMass σ selected z else 0 := by
    rw [← hβ, Finset.sum_image (e.injective.injOn)]
    simp_rw [hf]
  apply RealizationPoint.ext
  funext v
  change surgeryUnnormalizedWeight K σ hσ selected β f z v /
    surgeryNormalization σ selected β z =
    surgeryUnnormalizedWeight K σ hσ selected β' f' z v /
      surgeryNormalization σ selected β' z
  unfold surgeryUnnormalizedWeight surgeryNormalization
  rw [hcard, hsum]

end CurveComplex.WeightedFlowScratch
