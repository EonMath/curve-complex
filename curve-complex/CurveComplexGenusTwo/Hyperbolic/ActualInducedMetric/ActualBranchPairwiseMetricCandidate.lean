import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchSegmentTransitionCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainBranchLowerCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchNeighborhoodControl
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentBallRestrictionCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T2Space S] [CompactSpace E]

theorem actual_branch_chain_pairwise_local_metric (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∈ q.ramification) (i : Fin 6)
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)
      ⟨regularHexagonCandidate.vertex i,
        hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i⟩) :
    ∃ g ∈ actualCompactDevelopmentFamily q identify, x ∈ g.source ∧ g x = normalizedConeVertex ∧
      ∀ y ∈ g.source, ∀ z ∈ g.source,
        developmentChainEDist (actualCompactDevelopmentFamily q identify) y z = edist (g y) (g z) := by
  obtain ⟨e, hxe, hcenter, hcontract, htransition⟩ :=
    actual_branch_segment_transition_distance_bound q identify x hx i hposition
  let b : E → Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion) := fun y => identify (q.projection y)
  obtain ⟨V, hV, hxV, hVe⟩ := q.actual_branch_neighborhood_control x hx e.source e.open_source hxe
  have hIV : IsOpen (identify.symm ⁻¹' V) := hV.preimage identify.symm.continuous
  obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hIV (b x) (by simpa [b] using hxV)
  have hcover : b ⁻¹' Metric.ball (b x) R ⊆ e.source := by
    intro y hy
    apply hVe
    have h := hball hy
    simpa [b] using h
  obtain ⟨f, hxf, hfe, r, hr, htarget, hvalue, hfcontract⟩ :=
    contractive_development_ball_restriction b e x hxe hcontract
  let δ := min r (R / 8)
  have hδ : 0 < δ := lt_min hr (div_pos hR (by norm_num))
  have hδr : δ ≤ r := min_le_left _ _
  have hδR : δ ≤ R / 8 := min_le_right _ _
  let U := f.source ∩ f ⁻¹' Metric.ball (e x) δ
  have hU : IsOpen U := f.isOpen_inter_preimage Metric.isOpen_ball
  let g := f.restrOpen U hU
  have hgs : g.source ⊆ f.source := inter_subset_left
  have hge (y : E) : g y = e y := hvalue y
  have hxg : x ∈ g.source := by
    refine ⟨hxf, hxf, ?_⟩
    change dist (f x) (e x) < δ
    rw [hvalue]; simpa using hδ
  have hgt : g.target = Metric.ball (e x) δ := by
    ext v
    change v ∈ f.target ∩ f.symm ⁻¹' U ↔ v ∈ Metric.ball (e x) δ
    constructor
    · intro hv
      have h := hv.2.2
      change f (f.symm v) ∈ Metric.ball (e x) δ at h
      rwa [f.right_inv hv.1] at h
    · intro hv
      have hvf : v ∈ f.target := by
        rw [htarget]
        exact (Metric.ball_subset_ball hδr) hv
      refine ⟨hvf, f.map_target hvf, ?_⟩
      change f (f.symm v) ∈ Metric.ball (e x) δ
      rwa [f.right_inv hvf]
  have hg : g ∈ actualCompactDevelopmentFamily q identify := by
    refine ⟨e x, δ, hδ, hgt, ?_⟩
    intro y hy z hz
    simpa only [hge] using hcontract y (hfe (hgs hy)) z (hfe (hgs hz))
  have hnear (y : E) (hy : y ∈ g.source) : dist (e y) (e x) < δ := by
    have h := hy.2.2
    change dist (f y) (e x) < δ at h
    rwa [hvalue] at h
  refine ⟨g, hg, hxg, (hge x).trans hcenter, ?_⟩
  intro y hy z hz
  apply le_antisymm
  · exact developmentChainEDist_le_chain (by
      simpa only [add_zero] using DevelopmentChain.cons g hg hy hz (DevelopmentChain.nil z))
  · apply le_iInf; intro t
    apply le_iInf; intro hchain
    by_contra hn
    have hlt : t < edist (g y) (g z) := lt_of_not_ge hn
    have htfin : t ≠ ⊤ := ne_top_of_lt (hlt.trans_le le_top)
    have ht : t.toReal < dist (e y) (e z) := by
      have hh := (ENNReal.toReal_lt_toReal htfin (edist_ne_top (g y) (g z))).mpr hlt
      simpa only [edist_dist, ENNReal.toReal_ofReal dist_nonneg, hge] using hh
    have hby := hcontract y (hfe (hgs hy)) x hxe
    have hpair := dist_triangle (e y) (e x) (e z)
    have hzy := hnear z hz
    rw [dist_comm (e x) (e z)] at hpair
    have hbudget : dist (b y) (b x) + t.toReal < R := by
      have hyy := hnear y hy
      change dist (identify (q.projection y)) (identify (q.projection x)) + t.toReal < R
      linarith
    have hlower := developmentChain_branch_chart_lower_bound b
      (actualCompactDevelopmentFamily q identify)
      (by intro a ha; obtain ⟨c, s, hs, ht, hc⟩ := ha; exact ⟨c, s, ht⟩)
      (by intro a ha; obtain ⟨c, s, hs, ht, hc⟩ := ha; exact hc)
      e htransition (b x) R hcover hchain htfin hbudget
    linarith

end CurveComplex.Hyperbolic
