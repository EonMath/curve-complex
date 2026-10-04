import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBoundedSheetSeparationCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchNeighborhoodControl
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainLawsCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainSheetBarrierCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T2Space S] [CompactSpace E]

theorem actual_development_chain_ball_inside_open_neighborhood (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (U : Set E) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ R : ℝ, 0 < R ∧
      {y : E | developmentChainEDist (actualCompactDevelopmentFamily q identify) x y < ENNReal.ofReal R} ⊆ U := by
  let b := fun z : E => identify (q.projection z)
  let F := actualCompactDevelopmentFamily q identify
  have hballs : ∀ e ∈ F, ∃ c : H2, ∃ r : ℝ, e.target = Metric.ball c r := by
    intro e he
    obtain ⟨c, r, hr, ht, hc⟩ := he
    exact ⟨c, r, ht⟩
  have hcontract : ∀ e ∈ F, ∀ z ∈ e.source, ∀ w ∈ e.source,
      dist (b z) (b w) ≤ dist (e z) (e w) := by
    intro e he
    exact he.choose_spec.choose_spec.2.2
  have hbase (y : E) : edist (b x) (b y) ≤ developmentChainEDist F x y := by
    apply developmentChainEDist_base_lower_bound b F _ x y
    intro e he z hz w hw
    simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (hcontract e he z hz w hw)
  by_cases hxram : x ∈ q.ramification
  · obtain ⟨V, hV, hxV, hVU⟩ := q.actual_branch_neighborhood_control x hxram U hU hxU
    have hIV : IsOpen (identify '' V) := identify.isOpenMap V hV
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hIV (b x) ⟨q.projection x, hxV, rfl⟩
    refine ⟨R, hR, ?_⟩
    intro y hy
    have hdist : dist (b y) (b x) < R := by
      have hh := lt_of_le_of_lt (hbase y) hy
      rw [edist_dist, ENNReal.ofReal_lt_ofReal_iff hR] at hh
      exact (dist_comm _ _).trans_lt hh
    obtain ⟨v, hv, hveq⟩ := hball hdist
    have hq : v = q.projection y := identify.injective hveq
    have hqy : q.projection y ∈ V := hq ▸ hv
    exact hVU hqy
  · obtain ⟨V, hV, hxV, hVbranch, A, hA, hxA, hAV, hcover, hdisj, hAU⟩ :=
      actual_unramified_two_sheet_neighborhood_within q x hxram U hU hxU
    have hIV : IsOpen (identify '' V) := identify.isOpenMap V hV
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hIV (b x) ⟨q.projection x, hxV, rfl⟩
    let D := q.deck ⁻¹' A
    have hD : IsOpen D := hA.preimage q.deck.continuous
    have hAD : Disjoint A D := Set.disjoint_left.mpr (fun z hz hdz => hdisj z hz hdz)
    have hBD : b ⁻¹' Metric.ball (b x) R ⊆ A ∪ D := by
      intro z hz
      obtain ⟨v, hv, hvz⟩ := hball hz
      have hqz : q.projection z ∈ V := identify.injective hvz ▸ hv
      exact hcover z hqz
    refine ⟨R, hR, ?_⟩
    intro y hy
    apply hAU
    by_contra hyA
    have hlower := developmentChain_sheet_exit_lower_bound b F hballs hcontract
      A D hA hD hAD x y R hR hBD hxA hyA
    exact (not_le_of_gt hy) hlower

end CurveComplex.Hyperbolic
