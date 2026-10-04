import CurveComplexGenusTwo.Dependencies.ClosedDomain

namespace CurveComplex.SpherePort

/-- A planar Jordan closed-disc parametrization with exact boundary and interior
correspondence. Unlike the old Nonempty homeomorphism API, this states the two
properties needed by ComplementaryDiscSide. -/
theorem plane_inside_closed_disc_with_boundary (C : Set Schoenflies.Plane)
    (hC : Schoenflies.IsJordanCurve C) :
    ∃ e : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ closure (Schoenflies.inside C),
      (∀ x, (e x : Schoenflies.Plane) ∈ C ↔ ‖(x : Schoenflies.Plane)‖ = 1) ∧
      (∀ x, (e x : Schoenflies.Plane) ∈ Schoenflies.inside C ↔
        ‖(x : Schoenflies.Plane)‖ < 1) := by
  classical
  obtain ⟨e₀⟩ := hC.homeomorph_modelCurve
  obtain ⟨u, v, huv, _⟩ := Schoenflies.exists_isHomeoOn_of_homeomorph e₀
  obtain ⟨f, g, hfg, heq⟩ := Schoenflies.squareExtension C u v hC huv
  obtain ⟨h, hint, hcl, hfr⟩ :=
    exists_homeomorph_image_interior_closure_frontier_eq_unitBall
      (Schoenflies.Plane.convex_closedSquare 0 1)
      (by rw [Schoenflies.Plane.interior_closedSquare];
          exact ⟨0, by simp [Schoenflies.Plane.openSquare, Schoenflies.Plane.supNorm]⟩)
      (Schoenflies.Plane.isBounded_closedSquare 0 1)
  have hball : h '' Schoenflies.Plane.closedSquare 0 1 =
      Metric.closedBall (0 : Schoenflies.Plane) 1 := by
    simpa [Schoenflies.Plane.isClosed_closedSquare] using hcl
  have hcurve : h '' Schoenflies.modelCurve = Metric.sphere 0 1 := by
    simpa [Schoenflies.modelCurve_eq_frontier] using hfr
  have hfcurve : f '' C = Schoenflies.modelCurve :=
    (Set.EqOn.image_eq heq).trans huv.image_eq
  have hgcurve : g '' Schoenflies.modelCurve = C :=
    hfg.image_inv_eq (Set.subset_union_left) hfcurve
  have hclosure : closure (Schoenflies.inside C) = C ∪ Schoenflies.inside C :=
    ((Schoenflies.IsRegionOf.inside C).closure_eq
      (Schoenflies.jordan_curve_theorem hC)).trans (Set.union_comm _ _)
  let q : Schoenflies.Plane.closedSquare 0 1 ≃ₜ Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    Homeomorph.sets h (by
      ext x
      exact ⟨fun hx => hball ▸ Set.mem_image_of_mem h hx, fun hx => by
        obtain ⟨y, hy, hxy⟩ := hball.symm ▸ hx
        exact h.injective hxy ▸ hy⟩)
  let r : ↥(C ∪ Schoenflies.inside C) ≃ₜ Schoenflies.Plane.closedSquare 0 1 := {
    toFun := fun x => ⟨f x, hfg.mapsTo x.property⟩
    invFun := fun x => ⟨g x, hfg.mapsTo_inv x.property⟩
    left_inv := fun x => Subtype.ext (hfg.invOn.1 x.property)
    right_inv := fun x => Subtype.ext (hfg.invOn.2 x.property)
    continuous_toFun := Continuous.subtype_mk
      (continuousOn_iff_continuous_domRestrict.mp hfg.continuousOn) _
    continuous_invFun := Continuous.subtype_mk
      (continuousOn_iff_continuous_domRestrict.mp hfg.continuousOn_inv) _ }
  let e := q.symm.trans (r.symm.trans (Homeomorph.setCongr hclosure.symm))
  have hboundary (x : Metric.closedBall (0 : Schoenflies.Plane) 1) :
      (e x : Schoenflies.Plane) ∈ C ↔ ‖(x : Schoenflies.Plane)‖ = 1 := by
    change g (h.symm x) ∈ C ↔ ‖(x : Schoenflies.Plane)‖ = 1
    have hxq : h.symm x ∈ Schoenflies.Plane.closedSquare 0 1 := (q.symm x).property
    have hgiff : g (h.symm x) ∈ C ↔ h.symm x ∈ Schoenflies.modelCurve := by
      constructor
      · intro hx
        have : f (g (h.symm x)) ∈ Schoenflies.modelCurve :=
          hfcurve ▸ Set.mem_image_of_mem f hx
        rwa [hfg.invOn.2 hxq] at this
      · intro hx
        exact hgcurve ▸ Set.mem_image_of_mem g hx
    rw [hgiff]
    constructor
    · intro hx
      have : (x : Schoenflies.Plane) ∈ Metric.sphere 0 1 := by
        rw [← hcurve]
        exact ⟨h.symm x, hx, h.apply_symm_apply x⟩
      simpa [Metric.mem_sphere, dist_zero_right] using this
    · intro hx
      have : (x : Schoenflies.Plane) ∈ Metric.sphere 0 1 := by
        simpa [Metric.mem_sphere, dist_zero_right] using hx
      obtain ⟨z, hz, hzx⟩ := hcurve.symm ▸ this
      exact ((h.symm_apply_apply z).symm.trans (congrArg h.symm hzx)) ▸ hz
  refine ⟨e, hboundary, ?_⟩
  intro x
  have hxle : ‖(x : Schoenflies.Plane)‖ ≤ 1 := by
    simpa only [dist_zero_right] using (Metric.mem_closedBall.mp x.property)
  have hex : (e x : Schoenflies.Plane) ∈ C ∪ Schoenflies.inside C :=
    hclosure ▸ (e x).property
  constructor
  · intro hx
    have hn : (e x : Schoenflies.Plane) ∉ C :=
      Set.disjoint_right.mp (Schoenflies.disjoint_curve_inside C) hx
    exact lt_of_le_of_ne hxle (fun he => hn ((hboundary x).mpr he))
  · intro hx
    rcases hex with hb | hi
    · exact False.elim (hx.ne ((hboundary x).mp hb))
    · exact hi

end CurveComplex.SpherePort
