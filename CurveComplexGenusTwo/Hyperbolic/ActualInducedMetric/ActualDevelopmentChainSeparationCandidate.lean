import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualUnramifiedSheetSeparationCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.DevelopmentChainSheetBarrierCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actualCompactDevelopmentChainEDist_positive (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion)) (x y : E) (hne : x ≠ y) :
    0 < developmentChainEDist (actualCompactDevelopmentFamily q identify) x y := by
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
  have hbase : edist (b x) (b y) ≤ developmentChainEDist F x y := by
    clear hne
    apply le_iInf; intro r
    apply le_iInf; intro h
    induction h with
    | nil x => simp
    | @cons x y z t e he hx hy tail ih =>
      apply (edist_triangle (b x) (b y) (b z)).trans
      apply add_le_add _ ih
      simpa only [edist_dist] using ENNReal.ofReal_le_ofReal (hcontract e he x hx y hy)
  by_cases hproj : q.projection x = q.projection y
  · have hxram : x ∉ q.ramification := by
      intro hx
      have hfixed := (q.fixed_iff_branch x).mpr hx
      rcases (q.fiber_pair x y).mp hproj with heq | heq
      · exact hne heq.symm
      · exact hne (heq.trans hfixed).symm
    obtain ⟨V, hV, hxV, hVbranch, A, hA, hxA, hAV, hcover, hdisj⟩ :=
      actual_unramified_two_sheet_neighborhood q x hxram
    have hIV : IsOpen (identify '' V) := identify.isOpenMap V hV
    obtain ⟨R, hR, hball⟩ := Metric.isOpen_iff.mp hIV (b x) ⟨q.projection x, hxV, rfl⟩
    let D := q.deck ⁻¹' A
    have hD : IsOpen D := hA.preimage q.deck.continuous
    have hAD : Disjoint A D := Set.disjoint_left.mpr (fun z hz hdz => hdisj z hz hdz)
    have hBD : b ⁻¹' Metric.ball (b x) R ⊆ A ∪ D := by
      intro z hz
      obtain ⟨v, hv, hvz⟩ := hball hz
      have hqz : q.projection z ∈ V := by
        have hq : v = q.projection z := identify.injective hvz
        exact hq ▸ hv
      exact hcover z hqz
    have hyA : y ∉ A := by
      intro hy
      rcases (q.fiber_pair x y).mp hproj with heq | heq
      · exact hne heq.symm
      · exact hdisj x hxA (heq ▸ hy)
    have hlower := developmentChain_sheet_exit_lower_bound b F hballs hcontract
      A D hA hD hAD x y R hR hBD hxA hyA
    exact lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hR) hlower
  · have hbne : b x ≠ b y := fun h => hproj (identify.injective h)
    exact lt_of_lt_of_le (edist_pos.mpr hbne) hbase

end CurveComplex.Hyperbolic
