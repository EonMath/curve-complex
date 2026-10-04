import CurveComplexGenusTwo.Hyperbolic.CompactDoubleTopology

namespace CurveComplex.Hyperbolic
open Set Topology

theorem closedPolygon_interior_iff_not_frontier {P : Hexagon} (R : HexagonRegion P)
    (x : ClosedPolygon R) : (x : H2) ∈ R.interior ↔ (x : H2) ∉ frontier R.interior := by
  rw [frontier, R.open_interior.interior_eq]
  simp only [Set.mem_sdiff, x.property, true_and, not_not]

theorem polygon_double_left_interior_eq_compl_right {P : Hexagon} (R : HexagonRegion P) :
    Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior} =
    (Set.range (Metric.toGlueR (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R)))ᶜ := by
  classical
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨y, hy⟩
    have hb := ((polygon_double_cross_copy_eq_iff R x y).mp hy.symm).2
    exact (closedPolygon_interior_iff_not_frontier R x).mp hx hb
  · intro hz
    have hall : ∀ z : Metric.GlueSpace (boundaryInclusion_isometry R)
        (boundaryInclusion_isometry R), (∃ x, L x = z) ∨ ∃ y, Q y = z := by
      intro z
      refine Quotient.inductionOn z ?_
      intro v
      cases v with
      | inl x => exact Or.inl ⟨x, rfl⟩
      | inr y => exact Or.inr ⟨y, rfl⟩
    rcases hall z with ⟨x, rfl⟩ | ⟨y, hy⟩
    · refine ⟨x, (closedPolygon_interior_iff_not_frontier R x).mpr ?_, rfl⟩
      intro hx
      apply hz
      refine ⟨x, ?_⟩
      exact ((polygon_double_cross_copy_eq_iff R x x).mpr ⟨rfl, hx⟩).symm
    · exact False.elim (hz ⟨y, hy⟩)

theorem polygon_double_left_interior_isOpen {P : Hexagon} (R : HexagonRegion P) :
    IsOpen (Metric.toGlueL (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior}) := by
  rw [polygon_double_left_interior_eq_compl_right]
  exact (isCompact_range (Metric.toGlueR_isometry _ _).continuous).isClosed.isOpen_compl

theorem polygon_double_left_interior_hyperbolic_chart {P : Hexagon} (R : HexagonRegion P)
    (x : ClosedPolygon R) (hx : (x : H2) ∈ R.interior) :
    ∃ U : Set (Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)),
      IsOpen U ∧ Metric.toGlueL (boundaryInclusion_isometry R)
        (boundaryInclusion_isometry R) x ∈ U ∧
      ∃ f : U → H2, IsEmbedding f ∧ ∀ y z : U, dist y z = dist (f y) (f z) := by
  classical
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let U := L '' {x : ClosedPolygon R | (x : H2) ∈ R.interior}
  have he (z : U) : ∃ y : ClosedPolygon R, L y = z.val := by
    obtain ⟨y, _, hy⟩ := z.property
    exact ⟨y, hy⟩
  let g (z : U) : ClosedPolygon R := (he z).choose
  have hg (z : U) : L (g z) = z.val := (he z).choose_spec
  let f (z : U) : H2 := g z
  have hdist (y z : U) : dist (f y) (f z) = dist y z := by
    change dist (g y) (g z) = dist y.val z.val
    rw [← hg y, ← hg z]
    exact ((Metric.toGlueL_isometry _ _).dist_eq _ _).symm
  have hf : Isometry f := Isometry.of_dist_eq hdist
  exact ⟨U, polygon_double_left_interior_isOpen R, ⟨x, hx, rfl⟩,
    f, hf.isEmbedding, fun y z => (hdist y z).symm⟩

theorem polygon_double_left_interior_coordinates {P : Hexagon} (R : HexagonRegion P) :
    ∃ f : (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
      {x : ClosedPolygon R | (x : H2) ∈ R.interior}) → H2,
      Isometry f ∧ Set.range f = R.interior := by
  classical
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let U := L '' {x : ClosedPolygon R | (x : H2) ∈ R.interior}
  have he (z : U) : ∃ y : ClosedPolygon R, (y : H2) ∈ R.interior ∧ L y = z.val := z.property
  let g (z : U) : ClosedPolygon R := (he z).choose
  have hgi (z : U) : (g z : H2) ∈ R.interior := (he z).choose_spec.1
  have hg (z : U) : L (g z) = z.val := (he z).choose_spec.2
  let f (z : U) : H2 := g z
  have hdist (y z : U) : dist (f y) (f z) = dist y z := by
    change dist (g y) (g z) = dist y.val z.val
    rw [← hg y, ← hg z]
    exact ((Metric.toGlueL_isometry _ _).dist_eq _ _).symm
  refine ⟨f, Isometry.of_dist_eq hdist, ?_⟩
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    exact hgi y
  · intro hz
    let y : ClosedPolygon R := ⟨z, subset_closure hz⟩
    let v : U := ⟨L y, y, hz, rfl⟩
    refine ⟨v, ?_⟩
    have hy : g v = y := (Metric.toGlueL_isometry _ _).injective (hg v)
    exact congrArg Subtype.val hy

theorem polygon_double_left_interior_openPartialHomeomorph {P : Hexagon} (R : HexagonRegion P) :
    ∃ e : OpenPartialHomeomorph
      (Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)) H2,
      e.source = Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
        {x : ClosedPolygon R | (x : H2) ∈ R.interior} ∧ e.target = R.interior := by
  classical
  let U := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) ''
    {x : ClosedPolygon R | (x : H2) ∈ R.interior}
  have hU := polygon_double_left_interior_isOpen R
  obtain ⟨x, hx⟩ := R.nonempty_interior
  let : Nonempty U := ⟨⟨Metric.toGlueL (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R) ⟨x, subset_closure hx⟩,
    ⟨⟨x, subset_closure hx⟩, hx, rfl⟩⟩⟩
  obtain ⟨f, hf, hrange⟩ := polygon_double_left_interior_coordinates R
  have hopen : IsOpenEmbedding f := ⟨hf.isEmbedding, by rw [hrange]; exact R.open_interior⟩
  let s : TopologicalSpace.Opens
      (Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)) := ⟨U, hU⟩
  let c := s.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let d := hopen.toOpenPartialHomeomorph f
  refine ⟨c.symm.trans d, ?_, ?_⟩
  · simp [c, d, s, U]
  · simp [c, d, s, hrange]

end CurveComplex.Hyperbolic
