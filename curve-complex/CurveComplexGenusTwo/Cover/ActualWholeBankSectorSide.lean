import CurveComplexGenusTwo.Cover.FourDiskQuotient
import Mathlib.Analysis.Convex.GaugeRescale
import CurveComplexGenusTwo.Cover.AtlasComplete

open Set Metric Bornology
open scoped Topology
namespace AlternatingSphereCover

-- Actual sector-zero rays mapped to the two corners of the square's right side.
theorem actual_whole_bank_exact_sector_square_side : ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
    ∃ H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
      (∀ x, L x = (x 0 + x 1 / Real.sqrt 3, -x 0 + Real.sqrt 3 * x 1)) ∧
      (∀ p : Sphere, height p = 0 →
        (closedArcSector (0 : Fin 6) p ↔
          0 ≤ (L (horizontal p)).1 ∧
          |(L (horizontal p)).2| ≤ (L (horizontal p)).1)) ∧
      (∀ x, (H x).val = gaugeRescale
        (L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
        (Metric.closedBall (0 : ℝ × ℝ) 1) (L x.val)) ∧
      (∃ N : Set.range (northDiskFace false) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
       ∃ S : Set.range (southDiskFace true) ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1,
        (∀ x : StandardDisk, N ⟨northDiskFace false x,⟨x,rfl⟩⟩ = H x) ∧
        (∀ x : StandardDisk, S ⟨southDiskFace true x,⟨x,rfl⟩⟩ = H x)) ∧
      (∀ p : Sphere, ∀ hp : height p = 0,
        closedArcSector (0 : Fin 6) p ↔
          ((H (diskBoundaryPoint p hp)).val).1 = 1) := by
  obtain ⟨L,hL,hsector⟩ :
    ∃ L : EuclideanSpace ℝ (Fin 2) ≃L[ℝ] (ℝ × ℝ),
        (∀ x, L x = (x 0 + x 1 / Real.sqrt 3, -x 0 + Real.sqrt 3 * x 1)) ∧
        (∀ p : Sphere, height p = 0 →
          (closedArcSector (0 : Fin 6) p ↔
            0 ≤ (L (horizontal p)).1 ∧
            |(L (horizontal p)).2| ≤ (L (horizontal p)).1)) := by
    have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
    have hs₂ : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    let l : EuclideanSpace ℝ (Fin 2) ≃ₗ[ℝ] (ℝ × ℝ) := {
      toFun := fun x => (x 0 + x 1 / Real.sqrt 3, -x 0 + Real.sqrt 3 * x 1)
      invFun := fun z => !₂[(3*z.1-z.2)/4, Real.sqrt 3*(z.1+z.2)/4]
      left_inv := by
        intro x
        ext i
        fin_cases i
        · change (3*(x 0 + x 1 / Real.sqrt 3) - (-x 0 + Real.sqrt 3*x 1))/4 = x 0
          field_simp [hs.ne']
          ring_nf
          rw [hs₂]
          ring
        · change Real.sqrt 3*((x 0 + x 1 / Real.sqrt 3) + (-x 0 + Real.sqrt 3*x 1))/4 = x 1
          field_simp [hs.ne']
          ring_nf
          rw [hs₂]
          ring
      right_inv := by
        intro z
        apply Prod.ext
        · change (3*z.1-z.2)/4 + (Real.sqrt 3*(z.1+z.2)/4)/Real.sqrt 3 = z.1
          field_simp [hs.ne']
          ring
        · change -((3*z.1-z.2)/4) + Real.sqrt 3*(Real.sqrt 3*(z.1+z.2)/4) = z.2
          ring_nf
          rw [hs₂]
          ring
      map_add' := by intro x y; ext <;> simp <;> ring
      map_smul' := by intro a x; ext <;> simp <;> ring }
    let L := l.toContinuousLinearEquiv
    refine ⟨L,fun _ => rfl,?_⟩
    intro p hz
    change (height p = 0 ∧ 0 ≤ p.val 1 ∧ 0 ≤ seamA p ∧ 0 ≤ seamB p) ↔ _
    change (height p = 0 ∧ 0 ≤ p.val 1 ∧
        0 ≤ Real.sqrt 3 * p.val 0 - p.val 1 ∧
        0 ≤ Real.sqrt 3 * p.val 0 + p.val 1) ↔
      0 ≤ p.val 0 + p.val 1 / Real.sqrt 3 ∧
        |-p.val 0 + Real.sqrt 3 * p.val 1| ≤ p.val 0 + p.val 1 / Real.sqrt 3
    rw [abs_le]
    have hdiv : p.val 1 / Real.sqrt 3 = Real.sqrt 3 * p.val 1 / 3 := by
      field_simp [hs.ne']
      rw [hs₂]
    rw [hdiv]
    constructor
    · rintro ⟨_,hy,hA,hB⟩
      have hx : 0 ≤ p.val 0 := by nlinarith
      refine ⟨by positivity,?_,?_⟩ <;> nlinarith
    · rintro ⟨hu,hl,hr⟩
      refine ⟨hz,?_,?_,?_⟩ <;> nlinarith
  let s := L '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1
  let t := Metric.closedBall (0 : ℝ × ℝ) 1
  have hsc : Convex ℝ s := (convex_closedBall _ 1).linear_image L.toLinearMap
  have hscompact : IsCompact s := (isCompact_closedBall _ 1).image L.continuous
  have hs0 : s ∈ 𝓝 (0 : ℝ × ℝ) := by
    have hmem : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ 𝓝 0 :=
      closedBall_mem_nhds _ (by norm_num)
    have hpre : L.symm ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ∈ 𝓝 0 :=
      L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using hmem)
    change L.toHomeomorph.symm ⁻¹' _ ∈ 𝓝 0 at hpre
    rw [Homeomorph.preimage_symm] at hpre
    exact hpre
  have hsb : IsVonNBounded ℝ s :=
    NormedSpace.isVonNBounded_of_isBounded ℝ hscompact.isBounded
  have htc : Convex ℝ t := convex_closedBall _ 1
  have ht0 : t ∈ 𝓝 (0 : ℝ × ℝ) := closedBall_mem_nhds _ (by norm_num)
  have htb : IsVonNBounded ℝ t :=
    NormedSpace.isVonNBounded_of_isBounded ℝ isBounded_closedBall
  let g := gaugeRescaleHomeomorph s t hsc hs0 hsb htc ht0 htb
  let F := L.toHomeomorph.trans g
  have himage : F '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = t := by
    change (g ∘ L) '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 = t
    rw [Set.image_comp]
    have hg := image_gaugeRescaleHomeomorph_closure hsc hs0 hsb htc ht0 htb
    have htclosed : IsClosed t := isClosed_closedBall
    rw [hscompact.isClosed.closure_eq, htclosed.closure_eq] at hg
    exact hg
  let H : StandardDisk ≃ₜ Metric.closedBall (0 : ℝ × ℝ) 1 :=
    (F.image _).trans (Homeomorph.setCongr himage)
  have hright (p : Sphere) (hp : height p = 0) :
      closedArcSector (0 : Fin 6) p ↔ ((H (diskBoundaryPoint p hp)).val).1 = 1 := by
    have hn : ‖horizontal p‖ = 1 := by
      have hc := sphere_coordinate_squares p
      have hn₂ := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 2 => ℝ) (horizontal p)
      simp [Fin.sum_univ_succ, horizontal, Real.norm_eq_abs, sq_abs] at hn₂
      change ‖horizontal p‖^2 = (p.val 0)^2 + (p.val 1)^2 at hn₂
      have hp₂ : p.val 2 = 0 := hp
      rw [hp₂] at hc
      nlinarith only [hc, hn₂, norm_nonneg (horizontal p)]
    have hv : horizontal p ∈ frontier (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) := by
      rw [frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
      simpa only [mem_sphere, dist_zero_right] using hn
    have hzfront : L (horizontal p) ∈ frontier s := by
      change L.toHomeomorph (horizontal p) ∈ frontier
        (L.toHomeomorph '' Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      rw [← L.toHomeomorph.image_frontier]
      exact Set.mem_image_of_mem _ hv
    have hg₁ : gauge s (L (horizontal p)) = 1 :=
      (gauge_eq_one_iff_mem_frontier hsc hs0).mpr hzfront
    have hz : L (horizontal p) ≠ 0 := by
      intro hz
      have hh : horizontal p = 0 := L.injective (by simpa using hz)
      rw [hh,norm_zero] at hn
      norm_num at hn
    have hnz : ‖L (horizontal p)‖ ≠ 0 := (norm_pos_iff.mpr hz).ne'
    have hvalue : (H (diskBoundaryPoint p hp)).val =
        (1 / ‖L (horizontal p)‖) • L (horizontal p) := by
      change gaugeRescale s t (L (horizontal p)) = _
      rw [gaugeRescale,hg₁]
      dsimp only [t]
      rw [gauge_closedBall (by norm_num : (0 : ℝ) ≤ 1),div_one]
    rw [hvalue]
    change closedArcSector (0 : Fin 6) p ↔
      (1 / ‖L (horizontal p)‖) * (L (horizontal p)).1 = 1
    rw [one_div_mul_eq_div, div_eq_one_iff_eq hnz]
    rw [hsector p hp]
    constructor
    · rintro ⟨h₀,h₂⟩
      rw [Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg h₀,max_eq_left h₂]
    · intro he
      refine ⟨he ▸ norm_nonneg _,?_⟩
      rw [he,Prod.norm_def,Real.norm_eq_abs,Real.norm_eq_abs]
      exact le_max_right _ _
  letI : T2Space Total := actual_t2Space
  let qN : StandardDisk → Set.range (northDiskFace false) :=
    fun x => ⟨northDiskFace false x,⟨x,rfl⟩⟩
  have hqN : Continuous qN := (northDiskFace_continuous false).subtype_mk _
  have hqNi : Function.Injective qN := by
    intro x y h
    exact northDiskFace_injective false (congrArg Subtype.val h)
  have hqNs : Function.Surjective qN := by
    rintro ⟨y,⟨x,rfl⟩⟩
    exact ⟨x,rfl⟩
  let eN := Equiv.ofBijective qN ⟨hqNi,hqNs⟩
  let homeN : StandardDisk ≃ₜ Set.range (northDiskFace false) :=
    (show Continuous eN from hqN).homeoOfEquivCompactToT2
  let qS : StandardDisk → Set.range (southDiskFace true) :=
    fun x => ⟨southDiskFace true x,⟨x,rfl⟩⟩
  have hqS : Continuous qS := (southDiskFace_continuous true).subtype_mk _
  have hqSi : Function.Injective qS := by
    intro x y h
    exact southDiskFace_injective true (congrArg Subtype.val h)
  have hqSs : Function.Surjective qS := by
    rintro ⟨y,⟨x,rfl⟩⟩
    exact ⟨x,rfl⟩
  let eS := Equiv.ofBijective qS ⟨hqSi,hqSs⟩
  let homeS : StandardDisk ≃ₜ Set.range (southDiskFace true) :=
    (show Continuous eS from hqS).homeoOfEquivCompactToT2
  refine ⟨L,H,hL,hsector,fun _ => rfl,⟨homeN.symm.trans H,homeS.symm.trans H,?_,?_⟩,hright⟩
  · intro x
    change H (homeN.symm (homeN x)) = H x
    rw [homeN.symm_apply_apply]
  · intro x
    change H (homeS.symm (homeS x)) = H x
    rw [homeS.symm_apply_apply]

end AlternatingSphereCover
