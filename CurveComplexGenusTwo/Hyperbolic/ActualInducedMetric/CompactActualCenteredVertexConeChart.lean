import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalVertexCrossMetric
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnQuarterMetric

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_vertex_centered_cone_ball (i : Fin 6) :
    ∃ c : ClosedPolygon regularHexagonRegion,
      (c : H2) = regularHexagonCandidate.vertex i ∧ ∃ r : ℝ, ∃ hr : 0 < r,
      ∃ f : (Metric.ball
        (Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
          (boundaryInclusion_isometry regularHexagonRegion) c) r) → HalfTurnMetricCone,
        Isometry f ∧ ∃ p : H2, p.re = 0 ∧ p.im = 1 ∧
          Set.range f = Metric.ball (toHalfTurnMetricCone p) r ∧
          f ⟨Metric.toGlueL (boundaryInclusion_isometry regularHexagonRegion)
            (boundaryInclusion_isometry regularHexagonRegion) c, Metric.mem_ball_self hr⟩ =
              toHalfTurnMetricCone p := by
  classical
  obtain ⟨e, hxe, hxi, ε, he, hclosed, hcross⟩ := regularHexagon_actual_vertex_cross_metric i
  let R := regularHexagonRegion
  let x := regularHexagonCandidate.vertex i
  have hxf : x ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    exact Set.mem_iUnion.mpr ⟨i, by simp [Hexagon.edge, x]⟩
  let c : ClosedPolygon R := ⟨x, frontier_subset_closure hxf⟩
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : L c = Q c := (polygon_double_cross_copy_eq_iff R c c).mpr ⟨rfl, hxf⟩
  let U := Metric.ball (L c) r
  have hall (q : Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)) :
      (∃ a, L a = q) ∨ ∃ a, Q a = q := by
    refine Quotient.inductionOn q ?_
    intro v
    cases v with
    | inl a => exact Or.inl ⟨a, rfl⟩
    | inr a => exact Or.inr ⟨a, rfl⟩
  have hba (a : ClosedPolygon R) (hq : L a ∈ U) : (a : H2) ∈ Metric.ball x r := by
    change dist (L a) (L c) < r at hq
    rw [(Metric.toGlueL_isometry _ _).dist_eq] at hq
    exact hq
  have hbb (a : ClosedPolygon R) (hq : Q a ∈ U) : (a : H2) ∈ Metric.ball x r := by
    change dist (Q a) (L c) < r at hq
    rw [hc, (Metric.toGlueR_isometry _ _).dist_eq] at hq
    exact hq
  have hcoord (a : ClosedPolygon R) (ha : (a : H2) ∈ Metric.ball x r) :
      0 ≤ (e (a : H2)).re ∧ (e (a : H2)).re ^ 2 + (e (a : H2)).im ^ 2 ≤ 1 := by
    apply (hclosed (a : H2) ?_).mp a.property
    exact Metric.mem_ball.mpr (by have := Metric.mem_ball.mp ha; dsimp [r] at this; linarith)
  have hrepr (q : U) : ∃ a : ClosedPolygon R,
      (a : H2) ∈ Metric.ball x r ∧ (L a = q.val ∨ Q a = q.val) := by
    rcases hall q.val with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, hba a (ha ▸ q.property), Or.inl ha⟩
    · exact ⟨a, hbb a (ha ▸ q.property), Or.inr ha⟩
  let g (q : U) : ClosedPolygon R := (hrepr q).choose
  have hgball (q : U) : (g q : H2) ∈ Metric.ball x r := (hrepr q).choose_spec.1
  have hgrep (q : U) : L (g q) = q.val ∨ Q (g q) = q.val := (hrepr q).choose_spec.2
  let f (q : U) := if L (g q) = q.val then toHalfTurnMetricCone (e (g q : H2))
    else toHalfTurnMetricCone (unitCircleReflectionEquiv (e (g q : H2)))
  have hdist (q t : U) : dist (f q) (f t) = dist q t := by
    obtain ⟨hqr, hqn⟩ := hcoord (g q) (hgball q)
    obtain ⟨htr, htn⟩ := hcoord (g t) (hgball t)
    by_cases hq : L (g q) = q.val <;> by_cases ht : L (g t) = t.val
    · simp only [f, ite_eq_left hq, ite_eq_left ht]
      change _ = dist q.val t.val
      rw [halfTurnMetricCone_positive_quarter_distance _ _ hqr htr hqn htn,
        ← hq, ← ht, (Metric.toGlueL_isometry _ _).dist_eq, e.dist_eq]
      rfl
    · have htr' := (hgrep t).resolve_left ht
      simp only [f, ite_eq_left hq, ite_eq_right ht]
      change _ = dist q.val t.val
      rw [halfTurnMetricCone_cross_quarter_distance, ← hq, ← htr']
      exact (hcross (g q) (g t) (hgball q) (hgball t)).symm
    · have hqr' := (hgrep q).resolve_left hq
      simp only [f, ite_eq_right hq, ite_eq_left ht]
      change _ = dist q.val t.val
      rw [dist_comm, halfTurnMetricCone_cross_quarter_distance, ← hqr', ← ht,
        dist_comm (Q (g q)) (L (g t))]
      exact (hcross (g t) (g q) (hgball t) (hgball q)).symm
    · have hqr' := (hgrep q).resolve_left hq
      have htr' := (hgrep t).resolve_left ht
      simp only [f, ite_eq_right hq, ite_eq_right ht]
      change _ = dist q.val t.val
      rw [halfTurnMetricCone_unit_reflection_distance,
        halfTurnMetricCone_positive_quarter_distance _ _ hqr htr hqn htn,
        ← hqr', ← htr', (Metric.toGlueR_isometry _ _).dist_eq, e.dist_eq]
      rfl
  have hf : Isometry f := Isometry.of_dist_eq hdist
  have hLeft (a : ClosedPolygon R) (ha : L a ∈ U) :
      f ⟨L a, ha⟩ = toHalfTurnMetricCone (e (a : H2)) := by
    let q : U := ⟨L a, ha⟩
    have hga : g q = a := by
      rcases hgrep q with hl | hr
      · exact (Metric.toGlueL_isometry _ _).injective hl
      · exact ((polygon_double_cross_copy_eq_iff R a (g q)).mp hr.symm).1.symm
    have hgl : L (g q) = q.val := by rw [hga]
    change f q = _
    simp only [f, ite_eq_left hgl, hga]
  have hRight (a : ClosedPolygon R) (ha : Q a ∈ U) :
      f ⟨Q a, ha⟩ = toHalfTurnMetricCone (unitCircleReflectionEquiv (e (a : H2))) := by
    let q : U := ⟨Q a, ha⟩
    by_cases hl : L (g q) = q.val
    · obtain ⟨hga, hgf⟩ := (polygon_double_cross_copy_eq_iff R (g q) a).mp hl
      have hzero : dist (toHalfTurnMetricCone (e (a : H2)))
          (toHalfTurnMetricCone (unitCircleReflectionEquiv (e (a : H2)))) = 0 := by
        rw [halfTurnMetricCone_cross_quarter_distance, ← hcross a a (hbb a ha) (hbb a ha)]
        have hglue : L a = Q a := (polygon_double_cross_copy_eq_iff R a a).mpr ⟨rfl, hga ▸ hgf⟩
        change dist (L a) (Q a) = 0
        rw [hglue, dist_self]
      change f q = _
      simp only [f, ite_eq_left hl, hga]
      exact dist_eq_zero.mp hzero
    · have hrq := (hgrep q).resolve_left hl
      have hga : g q = a := (Metric.toGlueR_isometry _ _).injective hrq
      change f q = _
      simp only [f, ite_eq_right hl, hga]
  have hcball : L c ∈ U := Metric.mem_ball.mpr (by simpa using hr)
  have hfc : f ⟨L c, hcball⟩ = toHalfTurnMetricCone (e x) := hLeft c hcball
  have hrange : Set.range f = Metric.ball (toHalfTurnMetricCone (e x)) r := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      change dist (f q) (toHalfTurnMetricCone (e x)) < r
      rw [← hfc, hf.dist_eq]
      exact q.property
    · intro hw
      obtain ⟨⟨z⟩, rfl⟩ := SeparationQuotient.surjective_mk w
      have hzball : dist z (e x) < r := by
        change dist (toHalfTurnMetricCone z) (toHalfTurnMetricCone (e x)) < r at hw
        rwa [halfTurnMetricCone_center_distance z (e x) hxe hxi] at hw
      have hrep (v : H2) (hvball : dist v (e x) < r)
          (hvr : 0 ≤ v.re) (hvn : v.re ^ 2 + v.im ^ 2 ≤ 1) :
          ∃ a : ClosedPolygon R, (a : H2) ∈ Metric.ball x r ∧ e (a : H2) = v := by
        let a0 := e.symm v
        have hab : a0 ∈ Metric.ball x r := by
          change dist (e.symm v) x < r
          rw [← e.dist_eq (e.symm v) x, e.apply_symm_apply]
          exact hvball
        have haε : a0 ∈ Metric.ball x ε := Metric.mem_ball.mpr
          (by have := Metric.mem_ball.mp hab; dsimp [r] at this; linarith)
        have hac : a0 ∈ closure R.interior := (hclosed a0 haε).mpr
          (by simpa [a0] using And.intro hvr hvn)
        exact ⟨⟨a0, hac⟩, hab, e.apply_symm_apply v⟩
      have hvfix : verticalReflectionEquiv (e x) = e x := (verticalReflection_fixed_iff _).mpr hxe
      have hnfix : unitCircleReflectionEquiv (e x) = e x :=
        (unitCircleReflection_fixed_iff _).mpr (by rw [hxe, hxi]; norm_num)
      have hballV (v : H2) (hv : dist v (e x) < r) :
          dist (verticalReflectionEquiv v) (e x) < r := by
        rw [← hvfix, verticalReflectionEquiv.dist_eq]; exact hv
      have hballN (v : H2) (hv : dist v (e x) < r) :
          dist (unitCircleReflectionEquiv v) (e x) < r := by
        rw [← hnfix, unitCircleReflectionEquiv.dist_eq]; exact hv
      have hLa (a : ClosedPolygon R) (ha : (a : H2) ∈ Metric.ball x r) : L a ∈ U := by
        change dist (L a) (L c) < r
        rw [(Metric.toGlueL_isometry _ _).dist_eq]; exact ha
      have hQa (a : ClosedPolygon R) (ha : (a : H2) ∈ Metric.ball x r) : Q a ∈ U := by
        change dist (Q a) (L c) < r
        rw [hc, (Metric.toGlueR_isometry _ _).dist_eq]; exact ha
      by_cases hzre : 0 ≤ z.re <;> by_cases hzn : z.re ^ 2 + z.im ^ 2 ≤ 1
      · obtain ⟨a, ha, hev⟩ := hrep z hzball hzre hzn
        exact ⟨⟨L a, hLa a ha⟩, (hLeft a (hLa a ha)).trans (congrArg toHalfTurnMetricCone hev)⟩
      · obtain ⟨a, ha, hev⟩ := hrep (unitCircleReflectionEquiv z) (hballN z hzball)
          ((unitCircleReflection_nonnegative_real_iff z).mpr hzre)
          ((unitCircleReflection_closed_inner_iff_outer z).mpr (le_of_not_ge hzn))
        refine ⟨⟨Q a, hQa a ha⟩, ?_⟩
        rw [hRight a (hQa a ha), hev, unitCircleReflection_involutive]
        rfl
      · obtain ⟨a, ha, hev⟩ := hrep (verticalReflectionEquiv z) (hballV z hzball)
          (by rw [verticalReflection_re]; linarith)
          (by simpa only [verticalReflection_re, verticalReflection_im, neg_sq] using hzn)
        refine ⟨⟨Q a, hQa a ha⟩, ?_⟩
        rw [hRight a (hQa a ha), hev, vertex_reflections_commute]
        exact halfTurnMetricCone_halfTurn_eq z
      · obtain ⟨a, ha, hev⟩ := hrep (vertexHalfTurnEquiv z) (hballV _ (hballN z hzball))
          (by change 0 ≤ (verticalReflectionEquiv (unitCircleReflectionEquiv z)).re
              rw [verticalReflection_re, unitCircleReflection_re]
              exact neg_nonneg.mpr (div_nonpos_of_nonpos_of_nonneg (le_of_not_ge hzre)
                (by nlinarith [z.im_pos])))
          (by change (verticalReflectionEquiv (unitCircleReflectionEquiv z)).re ^ 2 +
                (verticalReflectionEquiv (unitCircleReflectionEquiv z)).im ^ 2 ≤ 1
              rw [verticalReflection_re, verticalReflection_im, neg_sq]
              exact (unitCircleReflection_closed_inner_iff_outer z).mpr (le_of_not_ge hzn))
        refine ⟨⟨L a, hLa a ha⟩, ?_⟩
        rw [hLeft a (hLa a ha), hev]
        exact halfTurnMetricCone_halfTurn_eq z
  exact ⟨c, rfl, r, hr, f, hf, e x, hxe, hxi, hrange, hfc⟩

end CurveComplex.Hyperbolic
