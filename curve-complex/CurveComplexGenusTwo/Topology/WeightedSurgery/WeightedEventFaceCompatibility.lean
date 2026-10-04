import CurveComplexGenusTwo.Topology.WeightedSurgery.WeightedSurgeryEvent

namespace CurveComplex.WeightedFlowScratch

variable {V B : Type*} [DecidableEq V] [DecidableEq B]

/-- One normalized branching event agrees on genuine overlapping barycentric
faces, including collisions among replacement labels. This is a property of
the explicit event formula, not an assumption of one already-existing flow. -/
theorem branchingSurgeryPoint_face_compatibility (K : AbstractSimplicialComplex V)
    (σ τ : Finset V) (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
    (a : V) (haσ : a ∈ σ) (haτ : a ∈ τ)
    (branches : Finset B) (hne : branches.Nonempty) (f : B → V)
    (hσnew : σ ∪ branches.image f ∈ K.faces)
    (hτnew : τ ∪ branches.image f ∈ K.faces)
    (x : FiniteSimplex σ) (y : FiniteSimplex τ)
    (hxy : faceInclusion K σ hσ x = faceInclusion K τ hτ y) (t : EdgeTime) :
    branchingSurgeryPoint K σ hσ ⟨a, haσ⟩ branches hne f hσnew (t, x) =
      branchingSurgeryPoint K τ hτ ⟨a, haτ⟩ branches hne f hτnew (t, y) := by
  have hw (v : V) : (faceInclusion K σ hσ x).weight v =
      (faceInclusion K τ hτ y).weight v := congrArg (fun p : RealizationPoint K => p.weight v) hxy
  have ha : x.val ⟨a, haσ⟩ = y.val ⟨a, haτ⟩ := by
    rw [← faceInclusion_weight_of_mem K σ hσ x a haσ,
      ← faceInclusion_weight_of_mem K τ hτ y a haτ]
    exact hw a
  apply RealizationPoint.ext
  funext v
  simp only [branchingSurgeryPoint, surgeryUnnormalizedWeight, surgeryNormalization,
    surgeryCutMass]
  rw [ha, hw v]

end CurveComplex.WeightedFlowScratch
