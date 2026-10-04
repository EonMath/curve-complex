import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualAnchorPointLocalChart
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualPrescribedNearbyContact

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The actual anchor alone supplies the base point chart, even away from all
source crossings. Source finite contacts choose a clear radius; every nearby
anchor point is reached, fixing all original contacts except the chosen base
point. This supplies local moves throughout the anchor complement intervals. -/
theorem actual_anchor_point_nearby_slide
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (F : Finset (EssentialArcClass M)) (P : FinitePosition M anchor F)
    (p : S) (hp : p ∈ arcInterior M anchor) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V, ∃ hpU : p ∈ U,
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (e ⟨p,hpU⟩).val = 0 ∧
      ∀ q : U, q.val ∈ anchor.val.image → |(e q).val 0| < ε →
      ∃ G : AmbientIsotopy S,
        (∀ t z, z ∈ M.cover.branch → G.map (t,z) = z) ∧
        (∀ t, (fun z => G.map (t,z)) '' anchor.val.image = anchor.val.image) ∧
        (∀ w z, z ∈ crossings M anchor (P.rep w) → z ≠ p → ∀ t, G.map (t,z) = z) ∧
        G.finalMap p = q.val := by
  obtain ⟨r,hrp⟩ := hp.1
  have hr : 0 < r.val ∧ r.val < 1 := anchor_interior_parameter_bounds M anchor r (hrp ▸ hp)
  obtain ⟨U,V,hU,e,hCV,hm,haxis,hpr,hpPlaneR⟩ := actual_anchor_parameter_axis_chart M anchor r hr
  have hpU : p ∈ U := hrp ▸ hpr
  have hpPlane : (e ⟨p,hpU⟩).val = 0 := by simpa only [hrp] using hpPlaneR
  obtain ⟨ε,hε,hε1,hmargin⟩ := actual_position_contact_coordinate_margin M anchor F P
    U V e haxis ⟨p,hpU⟩ hpPlane
  refine ⟨U,V,hU,e,hpU,ε,hε,hε1,hpPlane,?_⟩
  intro q hqa hqx
  let d : Plane ≃ₜ Plane := Homeomorph.smul (Units.mk0 ε⁻¹ (inv_ne_zero (ne_of_gt hε)))
  let V' : Set Plane := d '' V
  let e' : U ≃ₜ V' := e.trans (d.image V)
  have he' (z : U) (i : Fin 2) : (e' z).val i = (e z).val i / ε := by
    change ε⁻¹ * (e z).val i = _
    rw [div_eq_mul_inv,mul_comm]
  have hCV' : Plane.closedSquare 0 1 ⊆ V' := by
    intro z hz
    have hz0 : |z 0| ≤ 1 := (max_le_iff.mp (mem_closedSquare_zero_one.mp hz)).1
    have hz1 : |z 1| ≤ 1 := (max_le_iff.mp (mem_closedSquare_zero_one.mp hz)).2
    refine ⟨ε • z,hCV ?_,?_⟩
    · apply mem_closedSquare_zero_one.mpr
      change max |ε*z 0| |ε*z 1| ≤ 1
      rw [max_le_iff,abs_mul,abs_mul,abs_of_pos hε]
      constructor
      · exact (mul_le_mul_of_nonneg_left hz0 hε.le).trans (by simpa using hε1.le)
      · exact (mul_le_mul_of_nonneg_left hz1 hε.le).trans (by simpa using hε1.le)
    · change ε⁻¹ • (ε • z) = z
      rw [smul_smul,inv_mul_cancel₀ (ne_of_gt hε),one_smul]
  have haxis' (z : U) : z.val ∈ anchor.val.image ↔ (e' z).val 1 = 0 := by
    rw [he',div_eq_zero_iff]
    simp only [ne_of_gt hε,or_false]
    exact haxis z
  let a : Amount := ⟨(e q).val 0 / ε,by
    rw [abs_div,abs_of_pos hε]
    exact (div_lt_one hε).mpr hqx⟩
  obtain ⟨K,G,hmarks,hanchor,hout,hGU,hcoord⟩ :=
    actual_relative_crossing_slide M anchor U V' hU e' hCV' hm haxis' a
  refine ⟨G,hmarks,hanchor,?_,?_⟩
  · intro w z hz hne t
    by_cases hzU : z ∈ U
    · have hK : K.map (t,⟨z,hzU⟩) = ⟨z,hzU⟩ := by
        apply e'.injective
        apply Subtype.ext
        rw [hcoord]
        apply planeCoordinates.injective
        rw [planeIsotopy_coordinate]
        apply productIsotopy_fixed
        left
        change 1 ≤ |(e' ⟨z,hzU⟩).val 0|
        rw [he',abs_div,abs_of_pos hε]
        exact (le_div_iff₀ hε).mpr (by simpa using (hmargin w z hz hne hzU).le)
      rw [hGU t ⟨z,hzU⟩,hK]
    · exact hout t z hzU
  · have hp' : planeCoordinates (e' ⟨p,hpU⟩).val = (0,0) := by
      apply Prod.ext
      · change (e' ⟨p,hpU⟩).val 0 = 0
        rw [he',hpPlane]; simp
      · change (e' ⟨p,hpU⟩).val 1 = 0
        rw [he',hpPlane]; simp
    have hK : K.finalMap ⟨p,hpU⟩ = q := by
      apply e'.injective
      apply Subtype.ext
      apply planeCoordinates.injective
      change planeCoordinates (e' (K.map (1,⟨p,hpU⟩))).val = _
      rw [hcoord,planeIsotopy_coordinate,hp',productIsotopy_moves_crossing]
      apply Prod.ext
      · change 1*a.val = (e' q).val 0
        rw [he']; simp [a]
      · change 0 = (e' q).val 1
        exact ((haxis' q).mp hqa).symm
    exact (hGU 1 ⟨p,hpU⟩).trans (congrArg Subtype.val hK)
end
end CurveComplex.HyperellipticModel.ArcSurgery
