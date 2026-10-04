import CurveComplexGenusTwo.Topology.ActualFinitePositionSources.ActualMarkedEndpointSourceFanChart
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 5000000

theorem actual_selected_endpoint_germ_radius_below_avoided_cut
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M) (terminal : Bool)
    (r s : ℝ) (hr : 0 < r) (hrs : r < 1) (hs : 0 < s) (hss : s < 1)
    (W : Set S)
    (hGerm : range (c.val.map ∘ endpointGermParameter terminal r hr hrs) ⊆ W)
    (hCut : c.val.map (endpointGermParameter terminal s hs hss 1) ∉ W) : r < s := by
  by_contra hh
  have hsr : s ≤ r := le_of_not_gt hh
  let t : Interval := ⟨s/r,div_nonneg hs.le hr.le,(div_le_one hr).mpr hsr⟩
  have he : endpointGermParameter terminal r hr hrs t =
      endpointGermParameter terminal s hs hss 1 := by
    apply Subtype.ext
    cases terminal <;> dsimp [endpointGermParameter,t] <;> field_simp
  apply hCut
  apply hGerm
  exact ⟨t,congrArg c.val.map he⟩

theorem actual_endpoint_germ_range_mono_radius
    (M : HyperellipticModel E S) (c : EssentialMarkedArc M) (terminal : Bool)
    (r s : ℝ) (hr : 0 < r) (hrs : r < 1) (hs : 0 < s) (hss : s < 1)
    (hrs' : r ≤ s) :
    range (c.val.map ∘ endpointGermParameter terminal r hr hrs) ⊆
      range (c.val.map ∘ endpointGermParameter terminal s hs hss) := by
  rintro x ⟨t,rfl⟩
  let u : Interval := ⟨(r/s)*t.val,by
    constructor
    · exact mul_nonneg (div_nonneg hr.le hs.le) t.property.1
    · exact (mul_le_of_le_one_right (div_nonneg hr.le hs.le) t.property.2).trans
        ((div_le_one hs).mpr hrs')⟩
  refine ⟨u,?_⟩
  apply congrArg c.val.map
  apply Subtype.ext
  cases terminal <;> dsimp [endpointGermParameter,u] <;> field_simp
end CurveComplex.HyperellipticModel
