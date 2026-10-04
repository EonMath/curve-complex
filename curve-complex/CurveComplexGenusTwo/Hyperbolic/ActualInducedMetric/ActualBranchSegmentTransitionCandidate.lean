import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchRadialDevelopmentCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.BranchTransitionLocalBoundCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicSegmentNonexpansionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.HyperbolicMetricBallConvex
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentBallRestrictionCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actual_branch_segment_transition_distance_bound (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∈ q.ramification) (i : Fin 6)
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)
      ⟨regularHexagonCandidate.vertex i,
        hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) :
    ∃ e : OpenPartialHomeomorph E H2, x ∈ e.source ∧ e x = normalizedConeVertex ∧
      (∀ y ∈ e.source, ∀ z ∈ e.source,
        dist (identify (q.projection y)) (identify (q.projection z)) ≤ dist (e y) (e z)) ∧
      ∀ a ∈ actualCompactDevelopmentFamily q identify, ∀ y ∈ a.source, ∀ z ∈ a.source,
        (∀ v : H2, dist (a y) v + dist v (a z) = dist (a y) (a z) → a.symm v ∈ e.source) →
        dist (e y) (e z) ≤ dist (a y) (a z) := by
  obtain ⟨e, d, hxe, hcenter, hprojection, hdeck, hpunctured, hcontract, hradial⟩ :=
    actual_branch_radial_metric_development q identify x hx i hposition
  refine ⟨e, hxe, hcenter, hcontract, ?_⟩
  intro a ha y hy z hz hsegment
  obtain ⟨c, r, hr, htarget, hacontract⟩ := ha
  let s : Set H2 := a.target ∩ a.symm ⁻¹' e.source
  have hst : s ⊆ a.target := inter_subset_left
  have hse : ∀ v ∈ s, a.symm v ∈ e.source := fun v hv => hv.2
  have hmaps : MapsTo a.symm s e.source := hse
  have hcont : ContinuousOn (e ∘ a.symm) s :=
    e.continuousOn.comp (a.symm.continuousOn.mono hst) hmaps
  have hlocal := branch_transition_local_distance_bound
    (fun v => identify (q.projection v)) e a x hxe hradial hpunctured hacontract s hst hse
  have hseg : {v | dist (a y) v + dist v (a z) = dist (a y) (a z)} ⊆ s := by
    intro v hv
    refine ⟨?_, hsegment v hv⟩
    rw [htarget]
    have hay : a y ∈ Metric.ball c r := htarget ▸ a.map_source hy
    have haz : a z ∈ Metric.ball c r := htarget ▸ a.map_source hz
    exact metric_segment_stays_in_hyperbolic_ball c (a y) (a z) v hay haz hv
  have h := hyperbolic_segment_nonexpansion_of_local_bound (e ∘ a.symm) s hcont hlocal
    (a y) (a z) hseg
  simpa only [Function.comp_apply, a.left_inv hy, a.left_inv hz] using h

end CurveComplex.Hyperbolic
