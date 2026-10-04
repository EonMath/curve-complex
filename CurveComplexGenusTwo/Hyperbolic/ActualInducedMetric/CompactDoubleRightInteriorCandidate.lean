import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDoubleInteriorCharts

namespace CurveComplex.Hyperbolic
open Set Topology

theorem polygon_double_right_interior_eq_compl_left {P : Hexagon} (R : HexagonRegion P) :
    Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior} =
    (Set.range (Metric.toGlueL (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R)))ᶜ := by
  classical
  let L := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy⟩
    obtain ⟨heq, hb⟩ := (polygon_double_cross_copy_eq_iff R y x).mp hy
    have hbx : (x : H2) ∈ frontier R.interior := heq ▸ hb
    exact (closedPolygon_interior_iff_not_frontier R x).mp hx hbx
  · intro hz
    have hall : ∀ z : Metric.GlueSpace (boundaryInclusion_isometry R)
        (boundaryInclusion_isometry R), (∃ x, L x = z) ∨ ∃ y, Q y = z := by
      intro z
      refine Quotient.inductionOn z ?_
      intro v
      cases v with
      | inl x => exact Or.inr ⟨x, rfl⟩
      | inr y => exact Or.inl ⟨y, rfl⟩
    rcases hall z with ⟨x, rfl⟩ | ⟨y, hy⟩
    · refine ⟨x, (closedPolygon_interior_iff_not_frontier R x).mpr ?_, rfl⟩
      intro hx
      apply hz
      exact ⟨x, (polygon_double_cross_copy_eq_iff R x x).mpr ⟨rfl, hx⟩⟩
    · exact False.elim (hz ⟨y, hy⟩)

theorem polygon_double_right_interior_isOpen {P : Hexagon} (R : HexagonRegion P) :
    IsOpen (Metric.toGlueR (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior}) := by
  rw [polygon_double_right_interior_eq_compl_left]
  exact (isCompact_range (Metric.toGlueL_isometry _ _).continuous).isClosed.isOpen_compl

theorem polygon_double_right_interior_coordinates {P : Hexagon} (R : HexagonRegion P) :
    ∃ f : (Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior}) → H2,
      Isometry f ∧ Set.range f = R.interior := by
  classical
  let L := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let U := L '' {x : ClosedPolygon R | (x : H2) ∈ R.interior}
  have he (z : U) : ∃ y : ClosedPolygon R, (y : H2) ∈ R.interior ∧ L y = z.val := z.property
  let g (z : U) : ClosedPolygon R := (he z).choose
  have hgi (z : U) : (g z : H2) ∈ R.interior := (he z).choose_spec.1
  have hg (z : U) : L (g z) = z.val := (he z).choose_spec.2
  let f (z : U) : H2 := g z
  have hdist (y z : U) : dist (f y) (f z) = dist y z := by
    change dist (g y) (g z) = dist y.val z.val
    rw [← hg y, ← hg z]
    exact ((Metric.toGlueR_isometry _ _).dist_eq _ _).symm
  refine ⟨f, Isometry.of_dist_eq hdist, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact hgi y
  · intro hz
    let y : ClosedPolygon R := ⟨z, subset_closure hz⟩
    let v : U := ⟨L y, y, hz, rfl⟩
    refine ⟨v, ?_⟩
    have hy : g v = y := (Metric.toGlueR_isometry _ _).injective (hg v)
    exact congrArg Subtype.val hy


end CurveComplex.Hyperbolic
