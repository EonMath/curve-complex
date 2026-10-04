import CurveComplexGenusTwo.Hyperbolic.Stabilizer

namespace CurveComplex.Hyperbolic
open Set
variable {E : Type} [MetricSpace E]

theorem metric_chart_small_spheres_isometric (e : OpenPartialHomeomorph E H2)
    (x : E) (hx : x ∈ e.source)
    (hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source, dist y z = dist (e y) (e z)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, 0 < r → r < ε →
      Nonempty (Metric.sphere x r ≃ᵢ Metric.sphere (e x) r) := by
  obtain ⟨a, ha, hA⟩ := Metric.isOpen_iff.mp e.open_source x hx
  obtain ⟨b, hb, hB⟩ := Metric.isOpen_iff.mp e.open_target (e x) (e.map_source hx)
  refine ⟨min a b, lt_min ha hb, ?_⟩
  intro r hr hε
  have hra : r < a := hε.trans_le (min_le_left _ _)
  have hrb : r < b := hε.trans_le (min_le_right _ _)
  have hsrc (y : Metric.sphere x r) : y.val ∈ e.source := by
    apply hA
    change dist y.val x < a
    exact y.property.trans_lt hra
  have htgt (z : Metric.sphere (e x) r) : z.val ∈ e.target := by
    apply hB
    change dist z.val (e x) < b
    exact z.property.trans_lt hrb
  let f : Metric.sphere x r → Metric.sphere (e x) r := fun y =>
    ⟨e y, by
      change dist (e y.val) (e x) = r
      rw [← hmetric y (hsrc y) x hx]
      exact y.property⟩
  let g : Metric.sphere (e x) r → Metric.sphere x r := fun z =>
    ⟨e.symm z, by
      change dist (e.symm z.val) x = r
      rw [hmetric (e.symm z) (e.map_target (htgt z)) x hx, e.right_inv (htgt z)]
      exact z.property⟩
  refine ⟨{ toFun := f, invFun := g, left_inv := ?_, right_inv := ?_, isometry_toFun := ?_ }⟩
  · intro y
    apply Subtype.ext
    exact e.left_inv (hsrc y)
  · intro z
    apply Subtype.ext
    exact e.right_inv (htgt z)
  · apply Isometry.of_dist_eq
    intro y z
    exact (hmetric y (hsrc y) z (hsrc z)).symm

end CurveComplex.Hyperbolic
