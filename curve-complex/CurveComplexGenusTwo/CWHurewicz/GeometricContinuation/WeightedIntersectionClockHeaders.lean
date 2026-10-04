import CurveComplexGenusTwo.Topology.WeightedSurgery.FiniteRealizationTransport

namespace CurveComplex.WeightedFlowScratch

open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/- Anonymous probes for Hatcher's time t times theta. The coefficient function
is intrinsic intersection count; here any fixed coefficient function works. -/

theorem weightedThickness_face_compatible (K : AbstractSimplicialComplex V) (σ τ : Finset V)
    (hσ : σ ∈ K.faces) (hτ : τ ∈ K.faces)
    (x : FiniteSimplex σ) (y : FiniteSimplex τ) (c : V → ℝ)
    (hxy : faceInclusion K σ hσ x = faceInclusion K τ hτ y) :
    (∑ v ∈ σ, (faceInclusion K σ hσ x).weight v * c v) =
      ∑ v ∈ τ, (faceInclusion K τ hτ y).weight v * c v := by
  have hleft : (∑ v ∈ σ, (faceInclusion K σ hσ x).weight v * c v) =
      ∑ v ∈ σ ∪ τ, (faceInclusion K σ hσ x).weight v * c v := by
    apply Finset.sum_subset (Finset.subset_union_left)
    intro v _ hv
    rw [faceInclusion_weight_of_not_mem K σ hσ x v hv, zero_mul]
  have hright : (∑ v ∈ τ, (faceInclusion K τ hτ y).weight v * c v) =
      ∑ v ∈ σ ∪ τ, (faceInclusion K τ hτ y).weight v * c v := by
    apply Finset.sum_subset (Finset.subset_union_right)
    intro v _ hv
    rw [faceInclusion_weight_of_not_mem K τ hτ y v hv, zero_mul]
  rw [hleft, hright, hxy]

theorem weightedIntersectionDepth_continuous (K : AbstractSimplicialComplex V) (σ : Finset V)
    (hσ : σ ∈ K.faces) (c : V → ℝ) :
    Continuous (fun z : EdgeTime × FiniteSimplex σ =>
      z.1.val * ∑ v ∈ σ, (faceInclusion K σ hσ z.2).weight v * c v) := by
  apply (continuous_subtype_val.comp continuous_fst).mul
  apply continuous_finsetSum
  intro v _
  exact (((continuous_weight K v).comp (continuous_faceInclusion K σ hσ)).comp
    continuous_snd).mul continuous_const

end CurveComplex.WeightedFlowScratch
