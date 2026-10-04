import CurveComplexGenusTwo.Hyperbolic.CompactPolygonDisc
import CurveComplexGenusTwo.Hyperbolic.CompactDoubleTopology
import CurveComplexGenusTwo.Cover.HemisphereDisk

namespace CurveComplex.Hyperbolic
open Set Topology AlternatingSphereCover

theorem polygon_double_of_disc_is_sphere {P : Hexagon} (R : HexagonRegion P)
    (d : Metric.closedBall (0 : Schoenflies.Plane) 1 ≃ₜ ClosedPolygon R)
    (hboundary : ∀ x, (d x : H2) ∈ frontier R.interior ↔ ‖(x : Schoenflies.Plane)‖ = 1) :
    Nonempty (Metric.GlueSpace (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R) ≃ₜ Sphere) := by
  classical
  let L := Metric.toGlueL (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let Q := Metric.toGlueR (boundaryInclusion_isometry R) (boundaryInclusion_isometry R)
  let D : Sphere → Metric.closedBall (0 : Schoenflies.Plane) 1 :=
    coordinateDiskClosedBallHomeomorph ∘ diskProjection
  have hD : Continuous D := coordinateDiskClosedBallHomeomorph.continuous.comp diskProjection_continuous
  have hnorm (p : Sphere) :
      ‖(D p : Schoenflies.Plane)‖ ^ 2 = (p.val 0) ^ 2 + (p.val 1) ^ 2 := by
    change ‖horizontal p‖ ^ 2 = _
    rw [EuclideanSpace.real_norm_sq_eq]
    simp [horizontal, Fin.sum_univ_two, pow_two]
  have hzero (p : Sphere) : ‖(D p : Schoenflies.Plane)‖ = 1 ↔ height p = 0 := by
    have hs := sphere_coordinate_squares p
    have hn := hnorm p
    change ‖(D p : Schoenflies.Plane)‖ = 1 ↔ p.val 2 = 0
    constructor
    · intro h
      rw [h] at hn
      nlinarith
    · intro h
      rw [h] at hs
      nlinarith [norm_nonneg (D p : Schoenflies.Plane)]
  have hseam (p : Sphere) (hp : height p = 0) : L (d (D p)) = Q (d (D p)) :=
    (polygon_double_cross_copy_eq_iff R _ _).mpr ⟨rfl, (hboundary _).mpr ((hzero p).mpr hp)⟩
  let F : Sphere → Metric.GlueSpace (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R) := fun p => if 0 ≤ height p then L (d (D p)) else Q (d (D p))
  have hFn (p : Sphere) (hp : 0 ≤ height p) : F p = L (d (D p)) := if_pos hp
  have hFs (p : Sphere) (hp : height p ≤ 0) : F p = Q (d (D p)) := by
    by_cases hn : 0 ≤ height p
    · rw [hFn p hn]
      exact hseam p (le_antisymm hp hn)
    · exact if_neg hn
  have hF : Continuous F := by
    apply Continuous.if
    · intro p hp
      exact hseam p ((frontier_le_subset_eq continuous_const height_continuous hp).symm)
    · exact (Metric.toGlueL_isometry _ _).continuous.comp (d.continuous.comp hD)
    · exact (Metric.toGlueR_isometry _ _).continuous.comp (d.continuous.comp hD)
  have hDn (p q : Sphere) (hp : 0 ≤ height p) (hq : 0 ≤ height q)
      (heq : D p = D q) : p = q := by
    have hproj : diskProjection p = diskProjection q := coordinateDiskClosedBallHomeomorph.injective heq
    have hh : (⟨p, hp⟩ : NorthHemisphere) = ⟨q, hq⟩ := northDiskProjection_injective hproj
    exact congrArg Subtype.val hh
  have hDs (p q : Sphere) (hp : height p ≤ 0) (hq : height q ≤ 0)
      (heq : D p = D q) : p = q := by
    have hproj : diskProjection p = diskProjection q := coordinateDiskClosedBallHomeomorph.injective heq
    have hh : (⟨p, hp⟩ : SouthHemisphere) = ⟨q, hq⟩ := southDiskProjection_injective hproj
    exact congrArg Subtype.val hh
  have hcross (p q : Sphere) (hp : 0 ≤ height p) (hq : height q ≤ 0)
      (heq : L (d (D p)) = Q (d (D q))) : p = q := by
    obtain ⟨he, hb⟩ := (polygon_double_cross_copy_eq_iff R _ _).mp heq
    have hdpq : D p = D q := d.injective he
    have hz : height p = 0 := (hzero p).mp ((hboundary _).mp hb)
    have hzq : height q = 0 := (hzero q).mp (by
      rw [← hdpq]
      exact (hzero p).mpr hz)
    exact hDn p q hp (by rw [hzq]) hdpq
  have hinj : Function.Injective F := by
    intro p q heq
    by_cases hp : 0 ≤ height p
    · by_cases hq : 0 ≤ height q
      · rw [hFn p hp, hFn q hq] at heq
        exact hDn p q hp hq (d.injective ((Metric.toGlueL_isometry _ _).injective heq))
      · rw [hFn p hp, hFs q (le_of_not_ge hq)] at heq
        exact hcross p q hp (le_of_not_ge hq) heq
    · by_cases hq : 0 ≤ height q
      · rw [hFs p (le_of_not_ge hp), hFn q hq] at heq
        exact (hcross q p hq (le_of_not_ge hp) heq.symm).symm
      · rw [hFs p (le_of_not_ge hp), hFs q (le_of_not_ge hq)] at heq
        exact hDs p q (le_of_not_ge hp) (le_of_not_ge hq)
          (d.injective ((Metric.toGlueR_isometry _ _).injective heq))
  have hsurj : Function.Surjective F := by
    intro z
    refine Quotient.inductionOn z ?_
    intro v
    cases v with
    | inl x =>
      let v := coordinateDiskClosedBallHomeomorph.symm (d.symm x)
      obtain ⟨p, hp⟩ := northDiskProjection_surjective v
      refine ⟨p.val, ?_⟩
      rw [hFn p.val p.property]
      have hd : D p.val = d.symm x := by
        change coordinateDiskClosedBallHomeomorph (northDiskProjection p) = d.symm x
        rw [hp]
        exact coordinateDiskClosedBallHomeomorph.apply_symm_apply _
      rw [hd, d.apply_symm_apply]
      rfl
    | inr x =>
      let v := coordinateDiskClosedBallHomeomorph.symm (d.symm x)
      obtain ⟨p, hp⟩ := southDiskProjection_surjective v
      refine ⟨p.val, ?_⟩
      rw [hFs p.val p.property]
      have hd : D p.val = d.symm x := by
        change coordinateDiskClosedBallHomeomorph (southDiskProjection p) = d.symm x
        rw [hp]
        exact coordinateDiskClosedBallHomeomorph.apply_symm_apply _
      rw [hd, d.apply_symm_apply]
      rfl
  let k : Sphere ≃ Metric.GlueSpace (boundaryInclusion_isometry R)
      (boundaryInclusion_isometry R) := Equiv.ofBijective F ⟨hinj, hsurj⟩
  exact ⟨((show Continuous k from hF).homeoOfEquivCompactToT2).symm⟩

theorem regularHexagon_double_is_sphere :
    Nonempty (Metric.GlueSpace (boundaryInclusion_isometry regularHexagonRegion)
      (boundaryInclusion_isometry regularHexagonRegion) ≃ₜ Sphere) := by
  obtain ⟨d, hd⟩ := regularHexagon_closed_disc_with_boundary
  exact polygon_double_of_disc_is_sphere regularHexagonRegion d hd

end CurveComplex.Hyperbolic
