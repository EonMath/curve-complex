import Schoenflies.JordanSchoenflies
import Mathlib.Analysis.Convex.GaugeRescale

namespace CurveComplex.SpherePort

private noncomputable def restrictedHomeomorph {S T : Set Schoenflies.Plane}
    {f g : Schoenflies.Plane → Schoenflies.Plane}
    (h : Schoenflies.IsHomeoOn f g S T) : S ≃ₜ T where
  toFun x := ⟨f x, h.mapsTo x.property⟩
  invFun y := ⟨g y, h.mapsTo_inv y.property⟩
  left_inv x := Subtype.ext (h.invOn.1 x.property)
  right_inv y := Subtype.ext (h.invOn.2 y.property)
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp h.continuousOn
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuousOn_iff_continuous_domRestrict.mp h.continuousOn_inv

private noncomputable def squareBallHomeomorph :
    Schoenflies.Plane.closedSquare 0 1 ≃ₜ
      Metric.closedBall (0 : Schoenflies.Plane) 1 := by
  classical
  let witness :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Schoenflies.Plane.convex_closedSquare 0 1)
      (by rw [Schoenflies.Plane.interior_closedSquare]; exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
      (Schoenflies.Plane.isBounded_closedSquare 0 1)
  let h := Classical.choose witness
  have hclosed := (Classical.choose_spec witness).2.1
  have hclosed' : h '' Schoenflies.Plane.closedSquare 0 1 =
      Metric.closedBall (0 : Schoenflies.Plane) 1 := by
    simpa [h, Schoenflies.Plane.isClosed_closedSquare] using hclosed
  apply Homeomorph.sets h
  ext x
  constructor
  · intro hx
    exact hclosed' ▸ Set.mem_image_of_mem h hx
  · intro hx
    have : h x ∈ h '' Schoenflies.Plane.closedSquare 0 1 := hclosed'.symm ▸ hx
    rcases this with ⟨y, hy, hxy⟩
    exact h.injective hxy ▸ hy

theorem plane_inside_closed_disc (C : Set Schoenflies.Plane)
    (hC : Schoenflies.IsJordanCurve C) :
    Nonempty (Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ
      closure (Schoenflies.inside C)) := by
  obtain ⟨e⟩ := hC.homeomorph_modelCurve
  obtain ⟨u, v, huv, _⟩ := Schoenflies.exists_isHomeoOn_of_homeomorph e
  obtain ⟨f, g, hfg, _⟩ := Schoenflies.squareExtension C u v hC huv
  have hclosure : closure (Schoenflies.inside C) = C ∪ Schoenflies.inside C :=
    ((Schoenflies.IsRegionOf.inside C).closure_eq
      (Schoenflies.jordan_curve_theorem hC)).trans (Set.union_comm _ _)
  exact ⟨squareBallHomeomorph.symm.trans <|
    (restrictedHomeomorph hfg).symm.trans (Homeomorph.setCongr hclosure.symm)⟩

end CurveComplex.SpherePort
