import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import Mathlib

namespace CurveComplex.HyperellipticModel
open Set Topology Metric

/-- A radial half-collar shrinks by the actual distance to a closed obstacle.
Its width vanishes at the common boundary base and is positive elsewhere. -/
theorem closed_disk_relative_radial_half_collar
    (α : C(Interval,JordanClosedDisk))
    (hunit : ∀ s, ‖(α s).val‖ = 1) (hend : α 1 = α 0)
    (hinj : ∀ s s', α s = α s' →
      s = s' ∨ ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1)))
    (F : Set JordanPlane) (hF : IsClosed F) (hbase : (α 0).val ∈ F)
    (havoid : ∀ s ∈ Set.Ioo (0 : Interval) 1, (α s).val ∉ F) :
    ∃ β : C(Interval × Interval,JordanClosedDisk),
      (∀ s, β (s,0) = α s) ∧
      (∀ w, β (0,w) = α 0 ∧ β (1,w) = α 0) ∧
      (∀ s w s' w', β (s,w) = β (s',w') →
        (s = s' ∧ w = w') ∨
        ((s = 0 ∨ s = 1) ∧ (s' = 0 ∨ s' = 1))) ∧
      (∀ s w, β (s,w) ≠ α 0 → (β (s,w)).val ∉ F) ∧
      (∀ s ∈ Set.Ioo (0 : Interval) 1, ∀ w, 0 < w →
        ‖(β (s,w)).val‖ < 1) := by
  let δ : Interval → ℝ := fun s => min (1/4) (infDist (α s).val F/2)
  have hδc : Continuous δ := continuous_const.min
    (((Metric.continuous_infDist_pt F).comp
      (continuous_subtype_val.comp α.continuous)).div_const 2)
  have hδnonneg (s) : 0 ≤ δ s :=
    le_min (by norm_num) (div_nonneg infDist_nonneg (by norm_num))
  have hδupper (s) : δ s ≤ 1/4 := min_le_left _ _
  have hδdist (s) : δ s ≤ infDist (α s).val F/2 := min_le_right _ _
  have hδpos (s) (hs : s ∈ Set.Ioo (0 : Interval) 1) : 0 < δ s := by
    apply lt_min (by norm_num)
    exact div_pos ((hF.notMem_iff_infDist_pos ⟨_,hbase⟩).mp (havoid s hs)) (by norm_num)
  have hδzero : δ 0 = 0 := by
    simp only [δ,infDist_zero_of_mem hbase,zero_div]
    norm_num
  have hδone : δ 1 = 0 := by
    simpa only [δ,hend] using hδzero
  let R : Interval → Interval → ℝ := fun s w => 1-(w : ℝ)*δ s
  have hR (s w) : 0 < R s w ∧ R s w ≤ 1 := by
    have hm0 := mul_nonneg w.property.1 (hδnonneg s)
    have hm1 := (mul_le_of_le_one_left (hδnonneg s) w.property.2).trans (hδupper s)
    dsimp [R]
    constructor <;> linarith
  let β : C(Interval × Interval,JordanClosedDisk) :=
    ⟨fun z => ⟨R z.1 z.2 • (α z.1).val,by
      rw [Metric.mem_closedBall,dist_zero_right,norm_smul,Real.norm_eq_abs,
        abs_of_pos (hR z.1 z.2).1,hunit,mul_one]
      exact (hR z.1 z.2).2⟩,
      by
        apply Continuous.subtype_mk
        exact (continuous_const.sub (continuous_snd.subtype_val.mul
          (hδc.comp continuous_fst))).smul
            (continuous_subtype_val.comp (α.continuous.comp continuous_fst))⟩
  have hnorm (s w) : ‖(β (s,w)).val‖ = R s w := by
    change ‖R s w • (α s).val‖ = R s w
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (hR s w).1,hunit,mul_one]
  have hβzero (s) : β (s,0) = α s := by
    apply Subtype.ext
    change (1-(0 : ℝ)*δ s) • (α s).val = (α s).val
    simp
  have hβends (w) : β (0,w) = α 0 ∧ β (1,w) = α 0 := by
    constructor <;> apply Subtype.ext
    · change (1-(w : ℝ)*δ 0) • (α 0).val = (α 0).val
      rw [hδzero]
      simp
    · change (1-(w : ℝ)*δ 1) • (α 1).val = (α 0).val
      rw [hδone,hend]
      simp
  have hedge (s : Interval) (w : Interval) (hs : s = 0 ∨ s = 1) : β (s,w) = α 0 := by
    rcases hs with rfl | rfl
    · exact (hβends w).1
    · exact (hβends w).2
  have hinterior (s : Interval) (hs : s ≠ 0 ∧ s ≠ 1) : s ∈ Set.Ioo (0 : Interval) 1 :=
    ⟨bot_lt_iff_ne_bot.mpr hs.1,lt_top_iff_ne_top.mpr hs.2⟩
  refine ⟨β,hβzero,hβends,?_,?_,?_⟩
  · intro s w s' w' he
    have hr : R s w = R s' w' := by
      simpa only [hnorm] using congrArg (fun x : JordanClosedDisk => ‖x.val‖) he
    have hαeq : α s = α s' := by
      apply Subtype.ext
      have hv := congrArg Subtype.val he
      change R s w • (α s).val = R s' w' • (α s').val at hv
      rw [←hr] at hv
      have hc := congrArg (fun v : JordanPlane => (R s w)⁻¹ • v) hv
      simpa only [smul_smul,inv_mul_cancel₀ (hR s w).1.ne',one_smul] using hc
    rcases hinj s s' hαeq with hss | hs
    · subst s'
      by_cases hs0 : s = 0
      · exact Or.inr ⟨Or.inl hs0,Or.inl hs0⟩
      by_cases hs1 : s = 1
      · exact Or.inr ⟨Or.inr hs1,Or.inr hs1⟩
      left
      refine ⟨rfl,?_⟩
      apply Subtype.ext
      have hδ := hδpos s (hinterior s ⟨hs0,hs1⟩)
      dsimp [R] at hr
      nlinarith
    · exact Or.inr hs
  · intro s w hne hmem
    have hs0 : s ≠ 0 := fun hs => hne (hedge s w (Or.inl hs))
    have hs1 : s ≠ 1 := fun hs => hne (hedge s w (Or.inr hs))
    have hdpos : 0 < infDist (α s).val F :=
      (hF.notMem_iff_infDist_pos ⟨_,hbase⟩).mp (havoid s (hinterior s ⟨hs0,hs1⟩))
    have hdist : dist (α s).val (β (s,w)).val = (w : ℝ)*δ s := by
      rw [dist_eq_norm]
      change ‖(α s).val-(1-(w : ℝ)*δ s) • (α s).val‖ = _
      rw [show (α s).val-(1-(w : ℝ)*δ s) • (α s).val =
        ((w : ℝ)*δ s) • (α s).val from by module,
        norm_smul,Real.norm_eq_abs,hunit,mul_one]
      have hp := mul_nonneg w.property.1 (hδnonneg s)
      rw [abs_of_nonneg hp]
    have hbound := infDist_le_dist_of_mem hmem (x := (α s).val)
    rw [hdist] at hbound
    have hm := mul_le_of_le_one_left (hδnonneg s) w.property.2
    have hδd := hδdist s
    linarith
  · intro s hs w hw
    rw [hnorm]
    dsimp [R]
    have hp := mul_pos (show (0 : ℝ) < w.val from hw) (hδpos s hs)
    linarith

end CurveComplex.HyperellipticModel
