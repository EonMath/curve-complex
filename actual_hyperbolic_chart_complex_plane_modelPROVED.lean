import ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Hyperbolic.Cayley
open Set Topology
namespace CurveComplex.Hyperbolic
theorem actual_hyperbolic_chart_complex_plane_model {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
    (c : SmoothHyperbolicChart E) :
    ∃ e : OpenPartialHomeomorph E ℂ, e.source = c.chart.source ∧
      ∀ x (hx : x ∈ c.chart.source),
        let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
        e x = D (⟨c.chart x,c.upper x hx⟩ : H2) := by
  let D : H2 ≃ₜ ℂ := cayleyHomeomorph.trans (Homeomorph.unitBall (E := ℂ)).symm
  let e := (c.chart.toOpenPartialHomeomorph.trans UpperHalfPlane.ofComplex).transHomeomorph D
  have hs : e.source = c.chart.source := by
    ext x
    change (x ∈ c.chart.source ∧ c.chart x ∈ UpperHalfPlane.ofComplex.source) ↔
      x ∈ c.chart.source
    refine ⟨fun h => h.1,fun hx => ⟨hx,?_⟩⟩
    simp only [UpperHalfPlane.ofComplex,OpenPartialHomeomorph.symm_source,
      Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target]
    exact ⟨⟨c.chart x,c.upper x hx⟩,rfl⟩
  refine ⟨e,hs,?_⟩
  intro x hx
  change D (UpperHalfPlane.ofComplex (c.chart x)) = _
  rw [UpperHalfPlane.ofComplex_apply_of_im_pos (c.upper x hx)]
end CurveComplex.Hyperbolic
