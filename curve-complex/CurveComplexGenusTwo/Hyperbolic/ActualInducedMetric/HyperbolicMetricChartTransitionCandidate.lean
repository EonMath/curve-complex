import CurveComplexGenusTwo.Hyperbolic.Stabilizer

namespace CurveComplex.Hyperbolic
variable {E : Type} [MetricSpace E]

theorem hyperbolic_metric_chart_transition_distance
    (e d : OpenPartialHomeomorph E H2)
    (he : ∀ x ∈ e.source, ∀ y ∈ e.source, dist x y = dist (e x) (e y))
    (hd : ∀ x ∈ d.source, ∀ y ∈ d.source, dist x y = dist (d x) (d y)) :
    ∀ x ∈ (e.symm.trans d).source, ∀ y ∈ (e.symm.trans d).source,
      dist ((e.symm.trans d) x) ((e.symm.trans d) y) = dist x y := by
  intro x hx y hy
  change dist (d (e.symm x)) (d (e.symm y)) = dist x y
  rw [← hd (e.symm x) hx.2 (e.symm y) hy.2,
    he (e.symm x) (e.map_target hx.1) (e.symm y) (e.map_target hy.1),
    e.right_inv hx.1, e.right_inv hy.1]

end CurveComplex.Hyperbolic
