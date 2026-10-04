import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactDoubleRightInteriorCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentBallRestrictionCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem actual_right_interior_development_family_coverage (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∉ q.ramification)
    (hxi : identify (q.projection x) ∈
      Metric.toGlueR (boundaryInclusion_isometry regularHexagonRegion)
        (boundaryInclusion_isometry regularHexagonRegion) ''
        {y : ClosedPolygon regularHexagonRegion | (y : H2) ∈ regularHexagonRegion.interior}) :
    ∃ f ∈ actualCompactDevelopmentFamily q identify, x ∈ f.source := by
  classical
  let R := regularHexagonRegion
  let B := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let U : Set B := Metric.toGlueR (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R) '' {y : ClosedPolygon R | (y : H2) ∈ R.interior}
  have hU : IsOpen U := polygon_double_right_interior_isOpen R
  letI : Nonempty U := ⟨⟨identify (q.projection x), hxi⟩⟩
  obtain ⟨f, hf, hfrange⟩ := polygon_double_right_interior_coordinates R
  have hfo : IsOpenEmbedding f := ⟨hf.isEmbedding, by rw [hfrange]; exact R.open_interior⟩
  let s : TopologicalSpace.Opens B := ⟨U, hU⟩
  let a := s.openPartialHomeomorphSubtypeCoe (inferInstance : Nonempty U)
  let d := a.symm.trans (hfo.toOpenPartialHomeomorph f)
  have hds : d.source = U := by simp [d, a, s]
  obtain ⟨u, hux, huq, huinj⟩ := q.actual_unramified_chart x hx
  let e := (u.transHomeomorph identify).trans d
  have hxe : x ∈ e.source := by
    refine ⟨hux, ?_⟩
    change identify (u x) ∈ d.source
    rw [huq x, hds]
    exact hxi
  have hmetric : ∀ y ∈ e.source, ∀ z ∈ e.source,
      dist (identify (q.projection y)) (identify (q.projection z)) ≤ dist (e y) (e z) := by
    intro y hy z hz
    have hym : identify (q.projection y) ∈ U := by
      have hh : identify (u y) ∈ d.source := hy.2
      rwa [huq y, hds] at hh
    have hzm : identify (q.projection z) ∈ U := by
      have hh : identify (u z) ∈ d.source := hz.2
      rwa [huq z, hds] at hh
    have hyval : (a.symm (identify (q.projection y))).val = identify (q.projection y) := by
      apply a.right_inv
      simpa [a, s] using hym
    have hzval : (a.symm (identify (q.projection z))).val = identify (q.projection z) := by
      apply a.right_inv
      simpa [a, s] using hzm
    change _ ≤ dist (f (a.symm (identify (u y)))) (f (a.symm (identify (u z))))
    rw [huq y, huq z, hf.dist_eq]
    change _ ≤ dist (a.symm (identify (q.projection y))).val (a.symm (identify (q.projection z))).val
    rw [hyval, hzval]
  obtain ⟨g, hxg, hge, r, hr, htarget, hvalue, hgc⟩ :=
    contractive_development_ball_restriction (fun y => identify (q.projection y)) e x hxe hmetric
  refine ⟨g, ?_, hxg⟩
  exact ⟨e x, r, hr, htarget, hgc⟩

end CurveComplex.Hyperbolic
