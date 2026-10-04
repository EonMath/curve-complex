import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualBranchRadialDevelopmentCandidate

namespace CurveComplex.Hyperbolic
open Set
variable {E : Type} [TopologicalSpace E]

theorem branch_transition_local_distance_bound {B : Type} [MetricSpace B]
    (b : E → B) (e a : OpenPartialHomeomorph E H2) (x : E) (hx : x ∈ e.source)
    (hradial : ∀ y ∈ e.source, dist (b x) (b y) = dist (e x) (e y))
    (hpunctured : ∀ y ∈ e.source, y ≠ x → ∃ V : Set E, IsOpen V ∧ y ∈ V ∧ V ⊆ e.source ∧
      ∀ z ∈ V, ∀ w ∈ V, dist (e z) (e w) = dist (b z) (b w))
    (hcontract : ∀ y ∈ a.source, ∀ z ∈ a.source, dist (b y) (b z) ≤ dist (a y) (a z))
    (s : Set H2) (hst : s ⊆ a.target) (hse : ∀ z ∈ s, a.symm z ∈ e.source) :
    ∀ z ∈ s, ∃ ε : ℝ, 0 < ε ∧ ∀ w ∈ s, dist z w < ε →
      dist (e (a.symm z)) (e (a.symm w)) ≤ dist z w := by
  intro z hz
  have hzy : a.symm z ∈ a.source := a.map_target (hst hz)
  by_cases hzx : a.symm z = x
  · refine ⟨1, by norm_num, ?_⟩
    intro w hw hshort
    rw [hzx, ← hradial (a.symm w) (hse w hw)]
    have h := hcontract (a.symm z) hzy (a.symm w) (a.map_target (hst hw))
    have hax : a x = z := by rw [← hzx, a.right_inv (hst hz)]
    simpa only [hzx, hax, a.right_inv (hst hw)] using h
  · obtain ⟨V, hV, hyV, hVe, hmetric⟩ := hpunctured (a.symm z) (hse z hz) hzx
    have hU : IsOpen (a.target ∩ a.symm ⁻¹' V) := a.symm.isOpen_inter_preimage hV
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z ⟨hst hz, hyV⟩
    refine ⟨ε, hε, ?_⟩
    intro w hw hshort
    have hwV : a.symm w ∈ V := (hball (by simpa only [Metric.mem_ball, dist_comm] using hshort)).2
    rw [hmetric (a.symm z) hyV (a.symm w) hwV]
    have h := hcontract (a.symm z) hzy (a.symm w) (a.map_target (hst hw))
    simpa only [a.right_inv (hst hz), a.right_inv (hst hw)] using h

end CurveComplex.Hyperbolic
