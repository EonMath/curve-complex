import CurveComplexGenusTwo.Topology.GeometricPosition.WeightedBigonReplacement.ActualJordanDiskTools
import Mathlib.Analysis.Normed.Module.Normalize
import Schoenflies.JordanSchoenflies
open Set Topology Schoenflies
namespace CurveComplex

/-- Actual global circle coordinates for the source Jordan boundary. -/
theorem actual_jordan_global_unit_circle_chart
    (C : Set Plane) (hC : IsJordanCurve C) :
    ∃ F : Plane ≃ₜ Plane, F '' Metric.sphere (0 : Plane) 1 = C := by
  classical
  obtain ⟨e⟩ := hC.modelCurve_homeomorph
  obtain ⟨G,hG⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hC e
  obtain ⟨h,hi,hcl,hfront⟩ := exists_homeomorph_image_interior_closure_frontier_eq_unitBall
    (Plane.convex_closedSquare 0 1)
    (by rw [Plane.interior_closedSquare]; exact ⟨0,by simp [Plane.openSquare,Plane.supNorm]⟩)
    (Plane.isBounded_closedSquare 0 1)
  have hfront' : h '' modelCurve = Metric.sphere (0 : Plane) 1 := by
    simpa only [← modelCurve_eq_frontier] using hfront
  have hGC : G '' modelCurve = C := by
    ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      rw [hG ⟨y,hy⟩]
      exact (e ⟨y,hy⟩).property
    · intro hx
      refine ⟨(e.symm ⟨x,hx⟩).val,(e.symm ⟨x,hx⟩).property,?_⟩
      simpa only [e.apply_symm_apply] using hG (e.symm ⟨x,hx⟩)
  refine ⟨h.symm.trans G,?_⟩
  change (G ∘ h.symm) '' _ = C
  rw [Set.image_comp,←hfront']
  have hh : h.symm '' (h '' modelCurve) = modelCurve := by
    ext x
    simp
  rw [hh,hGC]

/-- Positive direction-dependent dilation has the explicit inverse dilation.
The regularity conditions are imposed on the radius, not on a desired support. -/
theorem actual_radial_dilation_inverse
    (R : Plane → ℝ) (hR : ∀ x, 0 < R x)
    (hRay : ∀ x (t : ℝ), 0 < t → R (t • x) = R x) :
    Function.LeftInverse (fun x => (R x)⁻¹ • x) (fun x => R x • x) ∧
    Function.RightInverse (fun x => (R x)⁻¹ • x) (fun x => R x • x) := by
  constructor
  · intro x
    dsimp only
    rw [hRay x (R x) (hR x),smul_smul,inv_mul_cancel₀ (ne_of_gt (hR x)),one_smul]
  · intro x
    dsimp only
    rw [hRay x (R x)⁻¹ (inv_pos.mpr (hR x)),smul_smul,
      mul_inv_cancel₀ (ne_of_gt (hR x)),one_smul]

/-- A bounded positive radius continuous off the origin yields a real plane
homeomorphism; continuity at the origin follows from the quantitative bound. -/
theorem actual_bounded_radial_homeomorphism
    (R : Plane → ℝ) (hlo : ∀ x, 1 ≤ R x) (hhi : ∀ x, R x ≤ 2)
    (hcont : ContinuousOn R {0}ᶜ)
    (hRay : ∀ x (t : ℝ), 0 < t → R (t • x) = R x) :
    ∃ H : Plane ≃ₜ Plane, (∀ x, H x = R x • x) ∧
      (∀ x, H.symm x = (R x)⁻¹ • x) := by
  have hpos (x : Plane) : 0 < R x := lt_of_lt_of_le zero_lt_one (hlo x)
  have hc : Continuous (fun x => R x • x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      refine ⟨ε/2,by positivity,?_⟩
      intro y hy
      simp only [smul_zero,dist_zero_right] at *
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hpos y)]
      calc R y * ‖y‖ ≤ 2 * ‖y‖ := mul_le_mul_of_nonneg_right (hhi y) (norm_nonneg _)
        _ < ε := by linarith
    · have hcR : ContinuousAt R x := (hcont x hx).continuousAt
        (isOpen_compl_singleton.mem_nhds hx)
      exact hcR.smul continuousAt_id
  have hci : Continuous (fun x => (R x)⁻¹ • x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x = 0
    · subst x
      apply Metric.continuousAt_iff.mpr
      intro ε hε
      refine ⟨ε,hε,?_⟩
      intro y hy
      simp only [smul_zero,dist_zero_right] at *
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (hpos y))]
      have hi : (R y)⁻¹ ≤ 1 := by
        exact (inv_le_one₀ (hpos y)).mpr (hlo y)
      calc (R y)⁻¹ * ‖y‖ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right hi (norm_nonneg _)
        _ < ε := by simpa using hy
    · have hcR : ContinuousAt R x := (hcont x hx).continuousAt
        (isOpen_compl_singleton.mem_nhds hx)
      exact (hcR.inv₀ (ne_of_gt (hpos x))).smul continuousAt_id
  obtain ⟨hleft,hright⟩ := actual_radial_dilation_inverse R hpos hRay
  exact ⟨{ toFun := fun x => R x • x
           invFun := fun x => (R x)⁻¹ • x
           left_inv := hleft
           right_inv := hright
           continuous_toFun := hc
           continuous_invFun := hci },fun _ => rfl,fun _ => rfl⟩

/-- The support radius is computed from the actual forbidden set. -/
theorem actual_distance_radial_homeomorphism (O : Set Plane) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ x, H x = (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x) ∧
      (∀ q ∈ Oᶜ, ‖q‖ = 1 → H q = q) := by
  let R : Plane → ℝ := fun x =>
    1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)
  have hlo (x : Plane) : 1 ≤ R x := by
    dsimp [R]
    have := Metric.infDist_nonneg (x := NormedSpace.normalize x) (s := Oᶜ)
    have : 0 ≤ min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2) :=
      le_min (by norm_num) (by positivity)
    linarith
  have hhi (x : Plane) : R x ≤ 2 := by
    dsimp [R]
    have := min_le_left (1 : ℝ) (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)
    linarith
  have hcont : ContinuousOn R {0}ᶜ := by
    apply continuousOn_of_forall_continuousAt
    intro x hx
    have hn : ContinuousAt (fun y : Plane => NormedSpace.normalize y) x := by
      exact ((continuousAt_id.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul continuousAt_id)
    exact continuousAt_const.add (continuousAt_const.min
      (((Metric.continuous_infDist_pt Oᶜ).continuousAt.comp hn).div_const 2))
  have hRay (x : Plane) (t : ℝ) (ht : 0 < t) : R (t • x) = R x := by
    dsimp [R]
    rw [NormedSpace.normalize_smul_of_pos ht]
  obtain ⟨H,hH,hInv⟩ := actual_bounded_radial_homeomorphism R hlo hhi hcont hRay
  refine ⟨H,hH,?_⟩
  intro q hq hnorm
  rw [hH]
  dsimp [R]
  rw [NormedSpace.normalize_eq_self_of_norm_eq_one hnorm,Metric.infDist_zero_of_mem hq]
  simp

/-- Every point moved from the open disk remains outside the actual forbidden
set, including directions through forbidden boundary endpoints. -/
theorem actual_distance_radial_open_support
    (O : Set Plane) (hball : Metric.ball (0 : Plane) 1 ⊆ O) :
    (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x) ''
      Metric.ball (0 : Plane) 1 ⊆ O := by
  rintro y ⟨x,hx,rfl⟩
  have hxnorm : ‖x‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hx
  let q := NormedSpace.normalize x
  let D := Metric.infDist q Oᶜ
  let ε := min 1 (D/2)
  have hD : 0 ≤ D := Metric.infDist_nonneg
  have hε : 0 ≤ ε := le_min (by norm_num) (by positivity)
  change (1+ε) • x ∈ O
  by_cases hxzero : x = 0
  · rw [hxzero,smul_zero]
    exact hball (by simp)
  have hqnorm : ‖q‖ = 1 := NormedSpace.norm_normalize hxzero
  let t := (1+ε) * ‖x‖
  have ht : 0 ≤ t := mul_nonneg (by linarith) (norm_nonneg _)
  have hxy : (1+ε) • x = t • q := by
    calc (1+ε) • x = (1+ε) • (‖x‖ • q) :=
        congrArg (fun z : Plane => (1+ε) • z) (NormedSpace.norm_smul_normalize x).symm
      _ = t • q := by rw [smul_smul]
  rw [hxy]
  by_cases htin : t < 1
  · apply hball
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg ht,hqnorm,mul_one] using htin
  have htlo : 1 ≤ t := le_of_not_gt htin
  have htupper : t < 1+ε := by
    dsimp [t]
    nlinarith only [hxnorm,hε]
  have hdist : dist q (t • q) = t-1 := by
    rw [dist_eq_norm]
    have he : q-t • q = (1-t) • q := by rw [sub_smul,one_smul]
    rw [he,norm_smul,Real.norm_eq_abs,hqnorm,mul_one,
      abs_of_nonpos (by linarith)]
    ring
  apply Metric.ball_infDist_compl_subset
  rw [Metric.mem_ball,dist_comm,hdist]
  change t-1 < D
  have heD : ε ≤ D/2 := min_le_right _ _
  linarith

/-- The whole compact enlarged disk stays in the actual chart domain. -/
theorem actual_distance_radial_closed_support
    (O Q : Set Plane) (hOQ : O ⊆ Q)
    (hball : Metric.ball (0 : Plane) 1 ⊆ O)
    (hsphere : Metric.sphere (0 : Plane) 1 ⊆ Q) :
    (fun x => (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x) ''
      Metric.closedBall (0 : Plane) 1 ⊆ Q := by
  rintro y ⟨x,hx,rfl⟩
  have hxnorm : ‖x‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hx
  let q := NormedSpace.normalize x
  let D := Metric.infDist q Oᶜ
  let ε := min 1 (D/2)
  have hD : 0 ≤ D := Metric.infDist_nonneg
  have hε : 0 ≤ ε := le_min (by norm_num) (by positivity)
  change (1+ε) • x ∈ Q
  by_cases hxzero : x = 0
  · rw [hxzero,smul_zero]
    exact hOQ (hball (by simp))
  have hqnorm : ‖q‖ = 1 := NormedSpace.norm_normalize hxzero
  let t := (1+ε) * ‖x‖
  have ht : 0 ≤ t := mul_nonneg (by linarith) (norm_nonneg _)
  have hxy : (1+ε) • x = t • q := by
    calc (1+ε) • x = (1+ε) • (‖x‖ • q) :=
        congrArg (fun z : Plane => (1+ε) • z) (NormedSpace.norm_smul_normalize x).symm
      _ = t • q := by rw [smul_smul]
  rw [hxy]
  by_cases htin : t < 1
  · apply hOQ; apply hball
    simpa only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg ht,hqnorm,mul_one] using htin
  have htlo : 1 ≤ t := le_of_not_gt htin
  have htupper : t ≤ 1+ε := by
    dsimp [t]
    nlinarith only [hxnorm,hε]
  by_cases hεzero : ε = 0
  · have hteq : t = 1 := by linarith
    rw [hteq,one_smul]
    apply hsphere
    simpa only [Metric.mem_sphere,dist_zero_right] using hqnorm
  have hεpos : 0 < ε := lt_of_le_of_ne hε (Ne.symm hεzero)
  apply hOQ
  apply Metric.ball_infDist_compl_subset
  rw [Metric.mem_ball,dist_comm,dist_eq_norm]
  have he : q-t • q = (1-t) • q := by rw [sub_smul,one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,hqnorm,mul_one,
    abs_of_nonpos (by linarith)]
  change -(1-t) < D
  have heD : ε ≤ D/2 := min_le_right _ _
  linarith

/-- Global Jordan coordinates identify the actual closed and open disk ranges. -/
theorem actual_global_jordan_closed_disk_range
    (C : Set Plane) (hC : IsJordanCurve C) (F : Plane ≃ₜ Plane)
    (hF : F '' Metric.sphere (0 : Plane) 1 = C) :
    F '' Metric.closedBall (0 : Plane) 1 = inside C ∪ C := by
  let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
    ⟨fun x => F x.val,F.continuous.comp continuous_subtype_val⟩
  have hd : Topology.IsEmbedding d := F.isEmbedding.comp Topology.IsEmbedding.subtypeVal
  have hb : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = C := by
    calc d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} =
        F '' Metric.sphere (0 : Plane) 1 := by
          ext y
          constructor
          · rintro ⟨x,hx,rfl⟩; exact ⟨x.val,hx,rfl⟩
          · rintro ⟨x,hx,rfl⟩
            exact ⟨⟨x,Metric.sphere_subset_closedBall hx⟩,hx,rfl⟩
      _ = C := hF
  have hr : Set.range d = F '' Metric.closedBall (0 : Plane) 1 := by
    ext y; constructor
    · rintro ⟨x,rfl⟩; exact ⟨x.val,x.property,rfl⟩
    · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
  rw [←hr]
  exact embedded_disc_range_eq_closed_inside d hd C hC hb

/-- Every real boundary point away from the retained endpoints becomes an
interior point of the proper support disk. -/
theorem actual_distance_radial_boundary_inside
    (O : Set Plane) (hO : IsOpen O) (hOc : Oᶜ.Nonempty)
    (H : Plane ≃ₜ Plane)
    (hH : ∀ x, H x = (1 + min 1 (Metric.infDist (NormedSpace.normalize x) Oᶜ / 2)) • x)
    (q : Plane) (hq : q ∈ O) (hqn : ‖q‖ = 1) :
    H.symm q ∈ Metric.ball (0 : Plane) 1 := by
  have hD : 0 < Metric.infDist q Oᶜ :=
    (hO.isClosed_compl.notMem_iff_infDist_pos hOc).mp (by simpa using hq)
  let R := 1 + min 1 (Metric.infDist q Oᶜ / 2)
  have hR : 1 < R := by
    have hp : 0 < min 1 (Metric.infDist q Oᶜ / 2) := lt_min (by norm_num) (by positivity)
    dsimp [R]; linarith
  have hp : 0 < R := by linarith
  have hinv : H.symm q = R⁻¹ • q := by
    apply H.injective
    rw [H.apply_symm_apply,hH,NormedSpace.normalize_smul_of_pos (inv_pos.mpr hp),
      NormedSpace.normalize_eq_self_of_norm_eq_one hqn]
    change q = R • (R⁻¹ • q)
    rw [smul_smul,mul_inv_cancel₀ (ne_of_gt hp),one_smul]
  rw [hinv]
  simp only [Metric.mem_ball,dist_zero_right,norm_smul,Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hp),hqn,mul_one]
  exact (inv_lt_one₀ hp).mpr hR

end CurveComplex
