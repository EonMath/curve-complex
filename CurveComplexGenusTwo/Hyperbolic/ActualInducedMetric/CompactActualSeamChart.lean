import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSeamCrossMetric
namespace CurveComplex.Hyperbolic
open Set Topology

theorem HexagonRegion.actual_seam_isometric_ball {P : Hexagon} (R : HexagonRegion P)
    (hP : P.IsEmbedded) (i : Fin 6) (x : H2) (hx : x ∈ P.edge i)
    (hxi : x ≠ P.vertex i) (hxn : x ≠ P.vertex (i + 1)) :
    ∃ c : ClosedPolygon R, (c : H2) = x ∧ ∃ r : ℝ, 0 < r ∧
      ∃ f : (Metric.ball
        (Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R) c) r) → H2,
        Isometry f ∧ ∃ y : H2, Set.range f = Metric.ball y r := by
  classical
  obtain ⟨e, hxe, ε, he, hfront, hclosed, hcross⟩ := R.actual_side_cross_metric hP i x hx hxi hxn
  have hxf : x ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    exact Set.mem_iUnion.mpr ⟨i, hx⟩
  let c : ClosedPolygon R := ⟨x, frontier_subset_closure hxf⟩
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let r := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : L c = Q c := ((polygon_double_cross_copy_eq_iff R c c).mpr ⟨rfl, hxf⟩)
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
  have hrepr (q : U) : ∃ a : ClosedPolygon R,
      (a : H2) ∈ Metric.ball x r ∧ (L a = q.val ∨ Q a = q.val) := by
    rcases hall q.val with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, hba a (ha ▸ q.property), Or.inl ha⟩
    · exact ⟨a, hbb a (ha ▸ q.property), Or.inr ha⟩
  let g (q : U) : ClosedPolygon R := (hrepr q).choose
  have hgball (q : U) : (g q : H2) ∈ Metric.ball x r := (hrepr q).choose_spec.1
  have hgrep (q : U) : L (g q) = q.val ∨ Q (g q) = q.val := (hrepr q).choose_spec.2
  let f (q : U) := if L (g q) = q.val then e (g q : H2)
    else verticalReflectionEquiv (e (g q : H2))
  have hdist (q t : U) : dist (f q) (f t) = dist q t := by
    by_cases hq : L (g q) = q.val <;> by_cases ht : L (g t) = t.val
    · simp only [f, ite_eq_left hq, ite_eq_left ht]
      change dist (e (g q : H2)) (e (g t : H2)) = dist q.val t.val
      rw [← hq, ← ht, (Metric.toGlueL_isometry _ _).dist_eq, e.dist_eq]
      rfl
    · have htr := (hgrep t).resolve_left ht
      simp only [f, ite_eq_left hq, ite_eq_right ht]
      change _ = dist q.val t.val
      rw [← hq, ← htr]
      exact (hcross (g q) (g t) (hgball q) (hgball t)).symm
    · have hqr := (hgrep q).resolve_left hq
      simp only [f, ite_eq_right hq, ite_eq_left ht]
      change _ = dist q.val t.val
      rw [← hqr, ← ht, dist_comm (Q (g q)) (L (g t)), dist_comm]
      exact (hcross (g t) (g q) (hgball t) (hgball q)).symm
    · have hqr := (hgrep q).resolve_left hq
      have htr := (hgrep t).resolve_left ht
      simp only [f, ite_eq_right hq, ite_eq_right ht]
      change _ = dist q.val t.val
      rw [← hqr, ← htr, verticalReflectionEquiv.dist_eq, e.dist_eq,
        (Metric.toGlueR_isometry _ _).dist_eq]
      rfl
  have hf : Isometry f := Isometry.of_dist_eq hdist
  have hLeft (a : ClosedPolygon R) (ha : L a ∈ U) : f ⟨L a, ha⟩ = e (a : H2) := by
    let q : U := ⟨L a, ha⟩
    have hga : g q = a := by
      rcases hgrep q with hl | hr
      · exact (Metric.toGlueL_isometry _ _).injective hl
      · exact ((polygon_double_cross_copy_eq_iff R a (g q)).mp hr.symm).1.symm
    have hgl : L (g q) = q.val := by rw [hga]
    change f q = _
    simp only [f, ite_eq_left hgl, hga]
  have hRight (a : ClosedPolygon R) (ha : Q a ∈ U) :
      f ⟨Q a, ha⟩ = verticalReflectionEquiv (e (a : H2)) := by
    let q : U := ⟨Q a, ha⟩
    by_cases hl : L (g q) = q.val
    · obtain ⟨hga, hgf⟩ := (polygon_double_cross_copy_eq_iff R (g q) a).mp hl
      have haf : (a : H2) ∈ frontier R.interior := hga ▸ hgf
      have hab : (a : H2) ∈ Metric.ball x ε := Metric.mem_ball.mpr
        (by have := Metric.mem_ball.mp (hbb a ha); dsimp [r] at this; linarith)
      have hafix := (verticalReflection_fixed_iff _).mpr ((hfront a hab).mp haf)
      change f q = _
      simp only [f, ite_eq_left hl, hga]
      exact hafix.symm
    · have hrq := (hgrep q).resolve_left hl
      have hga : g q = a := (Metric.toGlueR_isometry _ _).injective hrq
      change f q = _
      simp only [f, ite_eq_right hl, hga]
  have hcball : L c ∈ U := by exact Metric.mem_ball.mpr (by simpa using hr)
  have hfc : f ⟨L c, hcball⟩ = e x := hLeft c hcball
  have hrange : Set.range f = Metric.ball (e x) r := by
    ext w
    constructor
    · rintro ⟨q, rfl⟩
      change dist (f q) (e x) < r
      rw [← hfc, hf.dist_eq]
      exact q.property
    · intro hw
      have hw' : dist w (e x) < r := hw
      by_cases hwr : 0 ≤ w.re
      · let z := e.symm w
        have hzball : z ∈ Metric.ball x r := by
          change dist (e.symm w) x < r
          rw [← e.dist_eq (e.symm w) x, e.apply_symm_apply]
          exact hw'
        have hzl : z ∈ Metric.ball x ε := Metric.mem_ball.mpr
          (by have := Metric.mem_ball.mp hzball; dsimp [r] at this; linarith)
        have hzcl : z ∈ closure R.interior := (hclosed z hzl).mpr (by simpa [z] using hwr)
        let a : ClosedPolygon R := ⟨z, hzcl⟩
        have ha : L a ∈ U := by
          change dist (L a) (L c) < r
          rw [(Metric.toGlueL_isometry _ _).dist_eq]
          exact hzball
        exact ⟨⟨L a, ha⟩, (hLeft a ha).trans (e.apply_symm_apply w)⟩
      · let w' := verticalReflectionEquiv w
        have hwr' : 0 ≤ w'.re := by simp [w']; linarith
        have hwball : w' ∈ Metric.ball (e x) r := by
          have hcfix := (verticalReflection_fixed_iff _).mpr hxe
          have hd : dist w' (e x) = dist w (e x) := by
            calc
              _ = dist (verticalReflectionEquiv w) (verticalReflectionEquiv (e x)) :=
                congrArg (dist (verticalReflectionEquiv w)) hcfix.symm
              _ = dist w (e x) := verticalReflectionEquiv.dist_eq _ _
          exact Metric.mem_ball.mpr (hd ▸ hw')
        let z := e.symm w'
        have hzball : z ∈ Metric.ball x r := by
          change dist (e.symm w') x < r
          rw [← e.dist_eq (e.symm w') x, e.apply_symm_apply]
          exact hwball
        have hzl : z ∈ Metric.ball x ε := Metric.mem_ball.mpr
          (by have := Metric.mem_ball.mp hzball; dsimp [r] at this; linarith)
        have hzcl : z ∈ closure R.interior := (hclosed z hzl).mpr (by simpa [z] using hwr')
        let a : ClosedPolygon R := ⟨z, hzcl⟩
        have ha : Q a ∈ U := by
          change dist (Q a) (L c) < r
          rw [hc, (Metric.toGlueR_isometry _ _).dist_eq]
          exact hzball
        refine ⟨⟨Q a, ha⟩, ?_⟩
        rw [hRight a ha]
        change verticalReflectionEquiv (e (e.symm (verticalReflectionEquiv w))) = w
        rw [e.apply_symm_apply, verticalReflection_involutive]
  exact ⟨c, rfl, r, hr, f, hf, e x, hrange⟩
end CurveComplex.Hyperbolic
