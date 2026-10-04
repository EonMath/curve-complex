import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33ActualZeroComparison
import CurveComplexGenusTwo.Topology.LocalSurgery.ActualReturningSubarc

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [ChartedSpace Plane E]
set_option maxHeartbeats 4000000

/-- A positive-crossing original isotopic circle33 full-preimage pair has an
actual clean returning subarc and fixed-endpoint homotopy to a comparison path.
The strictly smaller actual representative is constructed by marked parallel
transport; no count-decrease certificate is added to the original input. -/
theorem circle33_actual_isotopic_intersection_has_returning_subarc
    (M : HyperellipticModel E S) (a b : EssentialCurve E) (c : Circle33 M)
    (hb : b.val.image = M.cover.projection ⁻¹' c.val.image)
    (ht : Transverse a.val b.val)
    (hiso : AmbientIsotopy.Rel a.val.image b.val.image)
    (hne : (a.val.image ∩ b.val.image).Nonempty) :
    ∃ u v : E, u ≠ v ∧ u ∈ a.val.image ∩ b.val.image ∧
      v ∈ a.val.image ∩ b.val.image ∧ ∃ f g : Path u v,
        IsEmbedding f ∧ range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
        f '' Set.Ioo (0 : Interval) 1 ⊆ b.val.imageᶜ ∧ f.Homotopic g := by
  classical
  letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
  obtain ⟨a',hi,ht',hzero⟩ := M.circle33_actual_isotopic_zero_comparison a b c hb hiso
  have hpos : 0 < ht.1.toFinset.card := by
    apply Finset.card_pos.mpr
    obtain ⟨x,hx⟩ := hne
    exact ⟨x,(Set.Finite.mem_toFinset ht.1).mpr hx⟩
  exact LocalSurgery.count_decreasing_isotopy_has_returning_subarc a b a' ht hi ht'
    (by rw [hzero]; exact hpos)
end CurveComplex.HyperellipticModel
