import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentFamilyProbe
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactActualSeamChart
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualDevelopmentBallRestrictionCandidate

namespace CurveComplex.Hyperbolic
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem actual_seam_base_metric_chart (q : BranchedDoubleCover E S)
    (identify : S ≃ₜ Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion))
    (x : E) (hx : x ∉ q.ramification)
    (c : ClosedPolygon regularHexagonRegion) (i : Fin 6)
    (hc : (c : H2) ∈ regularHexagonCandidate.edge i)
    (hci : (c : H2) ≠ regularHexagonCandidate.vertex i)
    (hcn : (c : H2) ≠ regularHexagonCandidate.vertex (i + 1))
    (hposition : identify (q.projection x) = Metric.toGlueL
      (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion) c) :
    ∃ f ∈ actualCompactDevelopmentFamily q identify, x ∈ f.source ∧
      ∀ y ∈ f.source, ∀ z ∈ f.source,
        dist (identify (q.projection y)) (identify (q.projection z)) = dist (f y) (f z) := by
  classical
  let R := regularHexagonRegion
  let B := Metric.GlueSpace (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  obtain ⟨c', hcc', ρ, hρ, f, hf, z, hfrange⟩ :=
    R.actual_seam_isometric_ball regularHexagonCandidate_embedded i c hc hci hcn
  have heqc : c' = c := Subtype.ext hcc'
  subst c'
  let U : Set B := Metric.ball (Metric.toGlueL (boundaryInclusion_isometry R)
    (boundaryInclusion_isometry R) c) ρ
  have hU : IsOpen U := Metric.isOpen_ball
  have hxi : identify (q.projection x) ∈ U := by
    rw [hposition]
    exact Metric.mem_ball_self hρ
  letI : Nonempty U := ⟨⟨identify (q.projection x), hxi⟩⟩
  have hfo : IsOpenEmbedding f := ⟨hf.isEmbedding, by rw [hfrange]; exact Metric.isOpen_ball⟩
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
      dist (identify (q.projection y)) (identify (q.projection z)) = dist (e y) (e z) := by
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
    change _ = dist (f (a.symm (identify (u y)))) (f (a.symm (identify (u z))))
    rw [huq y, huq z, hf.dist_eq]
    change _ = dist (a.symm (identify (q.projection y))).val (a.symm (identify (q.projection z))).val
    rw [hyval, hzval]
  obtain ⟨g, hxg, hge, r, hr, htarget, hvalue, hgc⟩ :=
    contractive_development_ball_restriction (fun y => identify (q.projection y)) e x hxe (fun y hy z hz => (hmetric y hy z hz).le)
  refine ⟨g, ⟨e x, r, hr, htarget, hgc⟩, hxg, ?_⟩
  intro y hy z hz
  rw [hvalue, hvalue]
  exact hmetric y (hge hy) z (hge hz)

end CurveComplex.Hyperbolic
