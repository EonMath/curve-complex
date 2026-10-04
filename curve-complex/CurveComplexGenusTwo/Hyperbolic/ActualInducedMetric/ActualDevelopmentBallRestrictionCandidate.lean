import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualVertexMetricDevelopmentCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E : Type} [TopologicalSpace E]

theorem contractive_development_ball_restriction {B : Type} [MetricSpace B] (b : E → B)
    (e : OpenPartialHomeomorph E H2) (x : E) (hx : x ∈ e.source)
    (hcontract : ∀ y ∈ e.source, ∀ z ∈ e.source, dist (b y) (b z) ≤ dist (e y) (e z)) :
    ∃ f : OpenPartialHomeomorph E H2, x ∈ f.source ∧ f.source ⊆ e.source ∧
      ∃ r : ℝ, 0 < r ∧ f.target = Metric.ball (e x) r ∧
        (∀ y : E, f y = e y) ∧
        ∀ y ∈ f.source, ∀ z ∈ f.source, dist (b y) (b z) ≤ dist (f y) (f z) := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  let U := e.source ∩ e ⁻¹' Metric.ball (e x) r
  have hU : IsOpen U := e.isOpen_inter_preimage Metric.isOpen_ball
  let f := e.restrOpen U hU
  have hsrc : f.source ⊆ e.source := Set.inter_subset_left
  have hxf : x ∈ f.source := ⟨hx, hx, Metric.mem_ball_self hr⟩
  have ht : f.target = Metric.ball (e x) r := by
    ext w
    change w ∈ e.target ∩ e.symm ⁻¹' U ↔ w ∈ Metric.ball (e x) r
    constructor
    · intro hw
      have hb := hw.2.2
      change e (e.symm w) ∈ Metric.ball (e x) r at hb
      rwa [e.right_inv hw.1] at hb
    · intro hw
      have hwt := hball hw
      refine ⟨hwt, e.map_target hwt, ?_⟩
      change e (e.symm w) ∈ Metric.ball (e x) r
      rwa [e.right_inv hwt]
  refine ⟨f, hxf, hsrc, r, hr, ht, fun _ => rfl, ?_⟩
  intro y hy z hz
  exact hcontract y (hsrc hy) z (hsrc hz)

end CurveComplex.Hyperbolic
