import CurveComplexGenusTwo.Cover.ActualWholeBankSectorSide
import Mathlib
open Set Metric Convexity
namespace AlternatingSphereCover
set_option maxHeartbeats 1600000
theorem actual_six_arc_parameterization : ∃ (P : Fin 6 → ℝ → Sphere) (Q : Fin 6 → Sphere → ℝ),
  (∀ i, Continuous (P i)) ∧
  (∀ i, Function.Injective (P i)) ∧
  (∀ i u, height (P i u) = 0) ∧
  (∀ i, P i '' Icc (-1) 1 = {p | closedArcSector i p}) ∧
  (∀ i, P i '' Ioo (-1) 1 = {p | arcSector i p}) ∧
  (∀ i, P i (-1) = branchPoint (cyclicBranch i)) ∧
  (∀ i, P i 1 = branchPoint (cyclicBranch (i + 1))) ∧
  (∀ i, ContinuousOn (Q i) (Set.range (P i))) ∧
  (∀ i u, Q i (P i u) = u) := by
  let V : Fin 6 → EuclideanSpace ℝ (Fin 3) := fun i => branchVector (cyclicBranch i)
  let D : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ :=
    fun v w => v 0 * w 1 - v 1 * w 0
  let d : ℝ := Real.sqrt 3 / 2
  have hs : 0 < Real.sqrt (3 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hs₂ : Real.sqrt (3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hd : 0 < d := by dsimp [d]; positivity
  have det : ∀ i, D (V i) (V (i + 1)) = d := by
    intro i
    fin_cases i <;> norm_num [V, D, d, cyclicBranch, branchVector] <;> ring
  have vz : ∀ i, V i 2 = 0 := by
    intro i
    fin_cases i <;> norm_num [V, cyclicBranch, branchVector]
  let C : Fin 6 → ℝ → EuclideanSpace ℝ (Fin 3) :=
    fun i u => (1 - u) • V i + (1 + u) • V (i + 1)
  have cn : ∀ i u, C i u ≠ 0 := by
    intro i u h
    have h₀ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 0) h
    have h₁ := congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v 1) h
    fin_cases i <;>
      norm_num [C, V, cyclicBranch, branchVector, PiLp.add_apply, PiLp.smul_apply] at h₀ h₁ <;>
      nlinarith
  let P : Fin 6 → ℝ → Sphere := fun i u =>
    ⟨‖C i u‖⁻¹ • C i u, by
      have hp : 0 < ‖C i u‖ := norm_pos_iff.mpr (cn i u)
      simp [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_of_pos hp, hp.ne']⟩
  let A : Fin 6 → EuclideanSpace ℝ (Fin 3) → ℝ := fun i p => D p (V (i + 1))
  let B : Fin 6 → EuclideanSpace ℝ (Fin 3) → ℝ := fun i p => D (V i) p
  have pc : ∀ i, Continuous (P i) := by
    intro i
    apply Continuous.subtype_mk
    change Continuous (fun u => ‖C i u‖⁻¹ • C i u)
    have cc : Continuous (C i) := by dsimp [C]; fun_prop
    exact (cc.norm.inv₀ (fun u => norm_ne_zero_iff.mpr (cn i u))).smul cc
  have ca : ∀ i u, A i (P i u).val = ‖C i u‖⁻¹ * (1 - u) * d := by
    intro i u
    calc
      A i (P i u).val = ‖C i u‖⁻¹ * (1 - u) * D (V i) (V (i + 1)) := by
        dsimp [A, P, C, D]
        ring
      _ = _ := by rw [det]
  have cb : ∀ i u, B i (P i u).val = ‖C i u‖⁻¹ * (1 + u) * d := by
    intro i u
    calc
      B i (P i u).val = ‖C i u‖⁻¹ * (1 + u) * D (V i) (V (i + 1)) := by
        dsimp [B, P, C, D]
        ring
      _ = _ := by rw [det]
  have pinj : ∀ i, Function.Injective (P i) := by
    intro i u v huv
    have ha := congrArg (fun p : Sphere => A i p.val) huv
    have hb := congrArg (fun p : Sphere => B i p.val) huv
    rw [ca, ca] at ha
    rw [cb, cb] at hb
    have hnu : 0 < ‖C i u‖ := norm_pos_iff.mpr (cn i u)
    have hnv : 0 < ‖C i v‖ := norm_pos_iff.mpr (cn i v)
    have hi : ‖C i u‖⁻¹ = ‖C i v‖⁻¹ := by nlinarith
    rw [← hi] at ha hb
    have hin : 0 < ‖C i u‖⁻¹ := inv_pos.mpr hnu
    have ht := mul_right_cancel₀ hd.ne' ha
    have ht' := mul_left_cancel₀ hin.ne' ht
    linarith
  have cpz : ∀ i u, height (P i u) = 0 := by
    intro i u
    dsimp [height, P, C]
    simp [vz]
  have sectorAB : ∀ (i : Fin 6) (p : Sphere),
      closedArcSector i p ↔ height p = 0 ∧ 0 ≤ A i p.val ∧ 0 ≤ B i p.val := by
    intro i p
    fin_cases i <;> dsimp [closedArcSector, A, B, D, V, cyclicBranch, branchVector, seamA, seamB]
    all_goals
      constructor
      · rintro ⟨hz, ha, hb, hc⟩
        exact ⟨hz, by linarith, by linarith⟩
      · rintro ⟨hz, ha, hb⟩
        exact ⟨hz, by linarith, by linarith, by linarith⟩
  have imageP : ∀ i, P i '' Icc (-1) 1 = {p | closedArcSector i p} := by
    intro i
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      change closedArcSector i (P i u)
      rw [sectorAB]
      refine ⟨cpz i u, ?_, ?_⟩
      · rw [ca]
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by linarith [hu.2])) hd.le
      · rw [cb]
        exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (by linarith [hu.1])) hd.le
    · intro hp
      change closedArcSector i p at hp
      obtain ⟨hz, ha, hb⟩ := (sectorAB i p).mp hp
      have hn : ‖p.val‖ = 1 := by simpa [mem_sphere_zero_iff_norm] using p.property
      have reconstruct : A i p.val • V i + B i p.val • V (i + 1) = d • p.val := by
        ext j
        fin_cases j
        · change A i p.val * V i 0 + B i p.val * V (i + 1) 0 = d * p.val 0
          rw [← det i]
          dsimp [A, B, D]
          ring
        · change A i p.val * V i 1 + B i p.val * V (i + 1) 1 = d * p.val 1
          rw [← det i]
          dsimp [A, B, D]
          ring
        · change A i p.val * V i 2 + B i p.val * V (i + 1) 2 = d * p.val 2
          change p.val 2 = 0 at hz
          simp [vz, hz]
      have hab : 0 < A i p.val + B i p.val := by
        by_contra h
        have ha0 : A i p.val = 0 := by linarith
        have hb0 : B i p.val = 0 := by linarith
        rw [ha0, hb0, zero_smul, zero_smul, zero_add] at reconstruct
        have hp0 : p.val = 0 := (smul_eq_zero.mp reconstruct.symm).resolve_left hd.ne'
        simp [hp0] at hn
      let u : ℝ := (B i p.val - A i p.val) / (A i p.val + B i p.val)
      have hu : u ∈ Icc (-1) 1 := by
        constructor
        · apply (le_div_iff₀ hab).mpr
          linarith
        · apply (div_le_iff₀ hab).mpr
          linarith
      let k : ℝ := 2 * d / (A i p.val + B i p.val)
      have hk : 0 < k := by dsimp [k]; positivity
      have ce : C i u = k • p.val := by
        calc
          C i u = (2 / (A i p.val + B i p.val)) •
              (A i p.val • V i + B i p.val • V (i + 1)) := by
            dsimp [C]
            rw [smul_add, smul_smul, smul_smul]
            congr 1
            · congr 1
              dsimp [u]
              field_simp [hab.ne']
              ring
            · congr 1
              dsimp [u]
              field_simp [hab.ne']
              ring
          _ = k • p.val := by
            rw [reconstruct, smul_smul]
            congr 1
            dsimp [k]
            ring
      refine ⟨u, hu, ?_⟩
      apply Subtype.ext
      change ‖C i u‖⁻¹ • C i u = p.val
      rw [ce, norm_smul, Real.norm_eq_abs, abs_of_pos hk, hn, mul_one, smul_smul]
      simp [hk.ne']
  have endpoint₀ : ∀ i, P i (-1) = branchPoint (cyclicBranch i) := by
    intro i
    apply Subtype.ext
    dsimp [P, C, V, branchPoint]
    have hn : ‖branchVector (cyclicBranch i)‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using branchVector_mem (cyclicBranch i)
    norm_num [norm_smul, Real.norm_eq_abs, hn, smul_smul]
  have endpoint₁ : ∀ i, P i 1 = branchPoint (cyclicBranch (i + 1)) := by
    intro i
    apply Subtype.ext
    dsimp [P, C, V, branchPoint]
    have hn : ‖branchVector (cyclicBranch (i + 1))‖ = 1 := by
      simpa [mem_sphere_zero_iff_norm] using branchVector_mem (cyclicBranch (i + 1))
    norm_num [norm_smul, Real.norm_eq_abs, hn, smul_smul]
  have closedNB : ∀ i p, closedArcSector i p ∧ ¬ branch p ↔ arcSector i p := by
    intro i p
    constructor
    · rintro ⟨hc, hn⟩
      have hpne : p.val 1 * seamA p * seamB p ≠ 0 := by
        rw [← seamPolynomial_factor]
        exact fun h => hn ⟨hc.1, h⟩
      have hyn : p.val 1 ≠ 0 := fun h => hpne (by simp [h])
      have han : seamA p ≠ 0 := fun h => hpne (by simp [h])
      have hbn : seamB p ≠ 0 := fun h => hpne (by simp [h])
      fin_cases i <;> dsimp [closedArcSector] at hc <;> dsimp [arcSector] <;>
        rcases hc with ⟨hz, hy, ha, hb⟩ <;>
        refine ⟨hz, ?_, ?_, ?_⟩ <;>
          first
          | exact lt_of_le_of_ne hy hyn.symm
          | exact lt_of_le_of_ne hy hyn
          | exact lt_of_le_of_ne ha han.symm
          | exact lt_of_le_of_ne ha han
          | exact lt_of_le_of_ne hb hbn.symm
          | exact lt_of_le_of_ne hb hbn

    · intro h
      exact ⟨arcSector_subset_closed h, arcSector_nonbranch h⟩
  have branchP : ∀ i u, u ∈ Icc (-1) 1 →
      (branch (P i u) ↔ u = -1 ∨ u = 1) := by
    intro i u hu
    have hc : closedArcSector i (P i u) := by
      have hm : P i u ∈ P i '' Icc (-1) 1 := ⟨u, hu, rfl⟩
      rw [imageP] at hm
      exact hm
    constructor
    · intro hb
      obtain ⟨j, hj⟩ := (branch_iff_cyclic_vertex (P i u)).mp hb
      rw [hj] at hc
      rcases (closedArcSector_branch_iff_endpoints i j).mp hc with hji | hji
      · left
        subst j
        apply pinj i
        exact hj.trans (endpoint₀ i).symm
      · right
        subst j
        apply pinj i
        exact hj.trans (endpoint₁ i).symm
    · rintro (rfl | rfl)
      · rw [endpoint₀]
        exact (branch_iff_cyclic_vertex _).mpr ⟨i, rfl⟩
      · rw [endpoint₁]
        exact (branch_iff_cyclic_vertex _).mpr ⟨i + 1, rfl⟩
  have openP : ∀ i, P i '' Ioo (-1) 1 = {p | arcSector i p} := by
    intro i
    ext p
    constructor
    · rintro ⟨u, hu, rfl⟩
      apply (closedNB i (P i u)).mp
      refine ⟨?_, ?_⟩
      · have hm : P i u ∈ P i '' Icc (-1) 1 := ⟨u, ⟨hu.1.le, hu.2.le⟩, rfl⟩
        rw [imageP] at hm
        exact hm
      · rw [branchP i u ⟨hu.1.le, hu.2.le⟩]
        rintro (h | h) <;> linarith [hu.1, hu.2]
    · intro hp
      change arcSector i p at hp
      obtain ⟨u, hu, rfl⟩ : p ∈ P i '' Icc (-1) 1 := by
        rw [imageP]
        exact arcSector_subset_closed hp
      have hn := arcSector_nonbranch hp
      have hu₀ : u ≠ -1 := fun h => hn ((branchP i u hu).mpr (Or.inl h))
      have hu₁ : u ≠ 1 := fun h => hn ((branchP i u hu).mpr (Or.inr h))
      exact ⟨u, ⟨lt_of_le_of_ne hu.1 hu₀.symm, lt_of_le_of_ne hu.2 hu₁⟩, rfl⟩
  let Q : Fin 6 → Sphere → ℝ := fun i p =>
    (B i p.val - A i p.val) / (A i p.val + B i p.val)
  have denom : ∀ i u, 0 < A i (P i u).val + B i (P i u).val := by
    intro i u
    rw [ca, cb]
    have hn : 0 < ‖C i u‖⁻¹ := inv_pos.mpr (norm_pos_iff.mpr (cn i u))
    have he : ‖C i u‖⁻¹ * (1 - u) * d + ‖C i u‖⁻¹ * (1 + u) * d =
        2 * ‖C i u‖⁻¹ * d := by ring
    rw [he]
    positivity
  have qc : ∀ i, ContinuousOn (Q i) (Set.range (P i)) := by
    intro i
    have ac : Continuous (fun p : Sphere => A i p.val) := by dsimp [A, D]; fun_prop
    have bc : Continuous (fun p : Sphere => B i p.val) := by dsimp [B, D]; fun_prop
    apply (bc.sub ac).continuousOn.div (ac.add bc).continuousOn
    rintro p ⟨u, rfl⟩
    exact (denom i u).ne'
  have qp : ∀ i u, Q i (P i u) = u := by
    intro i u
    have he : B i (P i u).val - A i (P i u).val =
        u * (A i (P i u).val + B i (P i u).val) := by rw [ca, cb]; ring
    dsimp only [Q]
    rw [he]
    exact mul_div_cancel_right₀ u (denom i u).ne'
  exact ⟨P, Q, pc, pinj, cpz, imageP, openP, endpoint₀, endpoint₁, qc, qp⟩
end AlternatingSphereCover
