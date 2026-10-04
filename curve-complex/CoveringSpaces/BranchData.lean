import CurveComplexGenusTwo.Topology.AlternatingSphereCover
import CurveComplexGenusTwo.Dictionary.BranchedCover

namespace AlternatingSphereCover

noncomputable def branchVector (i : Fin 6) : EuclideanSpace ℝ (Fin 3) :=
  (![!₂[1, 0, 0], !₂[-1, 0, 0],
     !₂[1/2, Real.sqrt 3/2, 0], !₂[1/2, -Real.sqrt 3/2, 0],
     !₂[-1/2, Real.sqrt 3/2, 0], !₂[-1/2, -Real.sqrt 3/2, 0]]) i

theorem branchVector_mem (i : Fin 6) : branchVector i ∈ Sphere := by
  change ‖branchVector i - 0‖ = 1
  rw [sub_zero]
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hn : ‖branchVector i‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    fin_cases i <;> norm_num [branchVector, Fin.sum_univ_succ, Real.norm_eq_abs,
      sq_abs] <;> nlinarith
  nlinarith [norm_nonneg (branchVector i)]

noncomputable def branchPoint (i : Fin 6) : Sphere := ⟨branchVector i, branchVector_mem i⟩

theorem branchPoint_injective : Function.Injective branchPoint := by
  intro i j h
  have h0 := congrArg (fun x : Sphere => x.val 0) h
  have h1 := congrArg (fun x : Sphere => x.val 1) h
  clear h
  have hs : 0 < Real.sqrt (3:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  fin_cases i <;> fin_cases j <;> try rfl
  all_goals try norm_num [branchPoint, branchVector] at h0
  all_goals try norm_num [branchPoint, branchVector] at h1
  all_goals linarith

theorem branch_iff_mem_range (x : Sphere) : branch x ↔ x ∈ Set.range branchPoint := by
  constructor
  · intro hb
    rcases hb with ⟨hz, hp⟩
    change x.val 2 = 0 at hz
    change x.val 1 * (3 * x.val 0 ^ 2 - x.val 1 ^ 2) = 0 at hp
    have hn : x.val 0 ^ 2 + x.val 1 ^ 2 + x.val 2 ^ 2 = 1 := by
      have hx : ‖x.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using x.property
      have hn := PiLp.norm_sq_eq_of_L2 (fun _ : Fin 3 => ℝ) x.val
      rw [hx] at hn
      simpa [Fin.sum_univ_succ, Real.norm_eq_abs, sq_abs, add_assoc] using hn.symm
    have hext (i : Fin 6) (h0 : x.val 0 = branchVector i 0)
        (h1 : x.val 1 = branchVector i 1) : branchPoint i = x := by
      apply Subtype.ext
      ext j
      fin_cases j
      · exact h0.symm
      · exact h1.symm
      · change branchVector i 2 = x.val 2
        rw [hz]
        fin_cases i <;> norm_num [branchVector]
    rcases mul_eq_zero.mp hp with hy | hp
    · have hx : x.val 0 = 1 ∨ x.val 0 = -1 :=
        (sq_eq_sq_iff_eq_or_eq_neg).mp (by nlinarith)
      rcases hx with hx | hx
      · exact ⟨0, hext 0 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
      · exact ⟨1, hext 1 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
    · have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
      have hx : x.val 0 = 1/2 ∨ x.val 0 = -(1/2) :=
        (sq_eq_sq_iff_eq_or_eq_neg).mp (by nlinarith)
      have hy : x.val 1 = Real.sqrt 3 / 2 ∨ x.val 1 = -(Real.sqrt 3 / 2) :=
        (sq_eq_sq_iff_eq_or_eq_neg).mp (by nlinarith)
      rcases hx with hx | hx <;> rcases hy with hy | hy
      · exact ⟨2, hext 2 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
      · exact ⟨3, hext 3 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
      · exact ⟨4, hext 4 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
      · exact ⟨5, hext 5 (by simpa [branchVector, neg_div] using hx) (by simpa [branchVector, neg_div] using hy)⟩
  · rintro ⟨i, rfl⟩
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
    fin_cases i <;> norm_num [branch, height, seamPolynomial, branchPoint, branchVector] <;>
      nlinarith

noncomputable def branchFinset : Finset Sphere := Finset.univ.image branchPoint

theorem branchFinset_card : branchFinset.card = 6 := by
  rw [branchFinset, Finset.card_image_of_injective _ branchPoint_injective]
  simp

theorem mem_branchFinset (x : Sphere) : x ∈ branchFinset ↔ branch x := by
  classical
  simpa [branchFinset] using (branch_iff_mem_range x).symm

theorem height_continuous : Continuous height := by
  unfold height
  fun_prop

theorem seamPolynomial_continuous : Continuous seamPolynomial := by
  unfold seamPolynomial
  fun_prop

theorem total_compact : CompactSpace Total := by
  have hh : Continuous (fun p : Sphere × Bool × Bool => height p.1) :=
    height_continuous.comp continuous_fst
  have hc : IsClosed {p : Sphere × Bool × Bool |
      if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} := by
    have he : {p : Sphere × Bool × Bool |
        if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} =
        {p | p.2.1 = false ∧ height p.1 ≤ 0} ∪
        {p | p.2.1 = true ∧ 0 ≤ height p.1} := by
      ext p
      cases h : p.2.1 <;> simp [h]
    rw [he]
    exact ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le hh continuous_const)).union
      ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le continuous_const hh))
  letI : CompactSpace Raw := isCompact_iff_compactSpace.mp hc.isCompact
  infer_instance

end AlternatingSphereCover
