import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualCrossingSlidePlane

namespace CurveComplex.ActualCrossingSlide
open Set Schoenflies
noncomputable section

def scaledPlaneSlide (ε : ℝ) (hε : 0 < ε) (a : Amount) : AmbientIsotopy Plane := by
  let e : Plane ≃ₜ Plane := Homeomorph.smul (Units.mk0 ε (ne_of_gt hε))
  exact {
    map := ⟨fun z => e ((planeIsotopy a).map (z.1,e.symm z.2)),
      e.continuous.comp ((planeIsotopy a).map.continuous.comp
        (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))⟩
    homeomorphism_at := fun t => ⟨(e.symm.trans
      ((planeCoordinates.trans (productSlide (timeAmount a t))).trans planeCoordinates.symm)).trans e,
      fun _ => rfl⟩
    at_zero := fun p => by
      change e ((planeIsotopy a).map (⟨0,by norm_num⟩,e.symm p)) = p
      rw [(planeIsotopy a).at_zero,e.apply_symm_apply] }

theorem scaledPlaneSlide_fixed (ε : ℝ) (hε : 0 < ε) (a : Amount)
    (t : Interval) (p : Plane) (hp : ε ≤ |p 0| ∨ ε ≤ |p 1|) :
    (scaledPlaneSlide ε hε a).map (t,p) = p := by
  let e : Plane ≃ₜ Plane := Homeomorph.smul (Units.mk0 ε (ne_of_gt hε))
  change e ((planeIsotopy a).map (t,e.symm p)) = p
  have hcoord (i : Fin 2) : (e.symm p) i = p i / ε := by
    change ε⁻¹ * p i = p i / ε
    rw [div_eq_mul_inv,mul_comm]
  have hfixed : (planeIsotopy a).map (t,e.symm p) = e.symm p := by
    apply planeCoordinates.injective
    rw [planeIsotopy_coordinate]
    apply productIsotopy_fixed
    change 1 ≤ |(e.symm p) 0| ∨ 1 ≤ |(e.symm p) 1|
    rcases hp with hp | hp
    · left; rw [hcoord,abs_div,abs_of_pos hε]; exact (le_div_iff₀ hε).mpr (by simpa using hp)
    · right; rw [hcoord,abs_div,abs_of_pos hε]; exact (le_div_iff₀ hε).mpr (by simpa using hp)
  rw [hfixed,e.apply_symm_apply]

theorem scaledPlaneSlide_fixed_outside_unit (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (a : Amount) (t : Interval) (p : Plane)
    (hp : p ∉ Plane.closedSquare 0 1) : (scaledPlaneSlide ε hε a).map (t,p) = p := by
  apply scaledPlaneSlide_fixed
  have hh : ¬ (|p 0| ≤ 1 ∧ |p 1| ≤ 1) := by
    intro hh; exact hp (by simpa only [mem_closedSquare_zero_one,Plane.supNorm,max_le_iff] using hh)
  rcases not_and_or.mp hh with hh | hh
  · exact Or.inl (hε1.trans (le_of_not_ge hh))
  · exact Or.inr (hε1.trans (le_of_not_ge hh))

theorem scaledPlaneSlide_second (ε : ℝ) (hε : 0 < ε) (a : Amount)
    (t : Interval) (p : Plane) : (scaledPlaneSlide ε hε a).map (t,p) 1 = p 1 := by
  change ε * ((planeIsotopy a).map (t,ε⁻¹ • p)) 1 = p 1
  rw [planeIsotopy_preserves_second]
  change ε * (ε⁻¹ * p 1) = p 1
  rw [← mul_assoc,mul_inv_cancel₀ (ne_of_gt hε),one_mul]

theorem scaledPlaneSlide_origin (ε : ℝ) (hε : 0 < ε) (a : Amount)
    (t : Interval) : (scaledPlaneSlide ε hε a).map (t,0) = Plane.mk (ε*t.val*a.val) 0 := by
  apply planeCoordinates.injective
  change planeCoordinates (ε • (planeIsotopy a).map (t,ε⁻¹ • (0:Plane))) = _
  rw [smul_zero]
  have hh := productIsotopy_moves_crossing a t
  have hc := planeIsotopy_coordinate a t 0
  have hp : planeCoordinates (0:Plane) = (0,0) := rfl
  rw [hp,hh] at hc
  apply Prod.ext
  · have hc0 := congrArg Prod.fst hc
    change ε * ((planeIsotopy a).map (t,0)) 0 = ε*t.val*a.val
    change ((planeIsotopy a).map (t,0)) 0 = t.val*a.val at hc0
    rw [hc0]; ring
  · have hc1 := congrArg Prod.snd hc
    change ε * ((planeIsotopy a).map (t,0)) 1 = 0
    change ((planeIsotopy a).map (t,0)) 1 = 0 at hc1
    rw [hc1,mul_zero]
end
end CurveComplex.ActualCrossingSlide
