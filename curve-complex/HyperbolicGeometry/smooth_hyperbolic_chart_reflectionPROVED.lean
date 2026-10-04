import ClosedHyperbolicCanonicalBridge
open Set Topology
open scoped Manifold ContDiff MatrixGroups ComplexConjugate
namespace CurveComplex.Hyperbolic
theorem smooth_hyperbolic_chart_reflection {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [MetricSpace E]
    (c : SmoothHyperbolicChart E) :
    ∃ d : SmoothHyperbolicChart E,
      d.chart.source = c.chart.source ∧ ∀ x, d.chart x = -conj (c.chart x) := by
  let L : ℂ ≃L[ℝ] ℂ := Complex.conjCLE.trans (ContinuousLinearEquiv.neg ℝ)
  let p := L.toDiffeomorph.toPartialDiffeomorph
  let d := c.chart.trans p
  have hs : d.source = c.chart.source := by
    ext x
    change (x ∈ c.chart.source ∧ c.chart x ∈ (Set.univ : Set ℂ)) ↔ x ∈ c.chart.source
    simp
  refine ⟨{ chart := d, upper := ?_, metric_preserving := ?_ },hs,fun x => rfl⟩
  · intro x hx
    have hc := c.upper x (hs ▸ hx)
    change 0 < (-conj (c.chart x)).im
    simpa using hc
  · intro x y
    have hx : x.val ∈ c.chart.source := hs ▸ x.property
    have hy : y.val ∈ c.chart.source := hs ▸ y.property
    rw [c.metric_preserving ⟨x.val,hx⟩ ⟨y.val,hy⟩]
    have hex (t : E) (ht : t ∈ d.source) :
        (⟨d t,by change 0 < (-conj (c.chart t)).im; simpa using c.upper t (hs ▸ ht)⟩ : H2) =
          UpperHalfPlane.J • (⟨c.chart t,c.upper t (hs ▸ ht)⟩ : H2) := by
      apply UpperHalfPlane.ext
      change -conj (c.chart t) = _
      rw [UpperHalfPlane.coe_J_smul]
    rw [hex x.val x.property,hex y.val y.property]
    symm
    simp only [UpperHalfPlane.dist_eq,UpperHalfPlane.coe_J_smul]
    simp only [←UpperHalfPlane.coe_im,UpperHalfPlane.coe_J_smul]
    simp [dist_neg_neg]
end CurveComplex.Hyperbolic
