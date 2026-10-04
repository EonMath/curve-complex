import CurveComplexGenusTwo.Dictionary.BranchedCover
open Set Topology Filter
namespace CurveComplex.BranchedDoubleCover
variable {E S X : Type} [TopologicalSpace E] [TopologicalSpace S] [TopologicalSpace X]

/-- A lift whose projection is continuous is automatically continuous at a
point over a branch value. Compactness prevents any other limiting fiber. -/
theorem continuousAt_of_branch_projection [CompactSpace E] [T2Space S]
    (q : BranchedDoubleCover E S) (g : X → E) (x : X)
    (hx : q.projection (g x) ∈ q.branch)
    (hπ : ContinuousAt (q.projection ∘ g) x) : ContinuousAt g x := by
  rw [ContinuousAt,Filter.tendsto_def]
  intro O hO
  obtain ⟨V,hVO,hV,hgx⟩ := mem_nhds_iff.mp hO
  let W : Set S := (q.projection '' Vᶜ)ᶜ
  have hW : IsOpen W :=
    (q.projection_continuous.isClosedMap Vᶜ hV.isClosed_compl).isOpen_compl
  have hxW : q.projection (g x) ∈ W := by
    rintro ⟨y,hy,hyp⟩
    have hfix := (q.fixed_iff_branch (g x)).mpr hx
    have hyx : y = g x := by
      rcases (q.fiber_pair (g x) y).mp hyp.symm with he | he
      · exact he
      · exact he.trans hfix
    exact hy (hyx.symm ▸ hgx)
  have hevent : (q.projection ∘ g) ⁻¹' W ∈ nhds x := hπ (hW.mem_nhds hxW)
  apply Filter.mem_of_superset hevent
  intro y hy
  apply hVO
  by_contra hn
  exact hy ⟨g y,hn,rfl⟩

end CurveComplex.BranchedDoubleCover
#print axioms CurveComplex.BranchedDoubleCover.continuousAt_of_branch_projection
