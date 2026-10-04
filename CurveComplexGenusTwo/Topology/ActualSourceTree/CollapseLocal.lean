import CurveComplexGenusTwo.Topology.GlobalArcCollar.WholeArcCollarReview
import Mathlib
open Set Metric Topology
namespace AlternatingSphereCover
/-- Fixed supported contraction of the central embedded interval. Intended for
an actual extended primal-tree strip; no contraction certificate is assumed. -/
theorem actual_central_arc_rectangle_collapse :
    let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
    let K : Set D := {v | v.1.val=0 ∧ |v.2.val|≤1}
    ∃ F : C(D,D),
      (∀ v, let r := max |v.1.val| (|v.2.val|-1)
        (F v).1.val=v.1.val ∧
        (F v).2.val=(1+1/max |v.1.val| 1)*(r/(1+r))*v.2.val) ∧
      Function.Surjective F ∧
      (∀ v w, F v=F w ↔ v=w ∨ (v∈K ∧ w∈K)) ∧
      (∀ v, (|v.1.val|=2 ∨ |v.2.val|=2) → F v=v) := by
  let collapseR (a y : ℝ) := max a (|y| - 1)
  let collapseQ (a y : ℝ) := collapseR a y / (1 + collapseR a y) * y
  let collapseY (a y : ℝ) := (1 + 1 / max a 1) * collapseQ a y
  have collapseR_nonneg {a y : ℝ} (ha : 0 ≤ a) : 0 ≤ collapseR a y :=
    ha.trans (le_max_left _ _)
  have collapseQ_abs {a y : ℝ} (ha : 0 ≤ a) : |collapseQ a y| = collapseQ a |y| := by
    have hr := collapseR_nonneg (y := y) ha
    simp only [collapseQ, abs_mul, abs_div]
    rw [abs_of_nonneg hr, abs_of_pos (show 0 < 1 + collapseR a y by linarith)]
    simp only [collapseR, abs_abs]
  have collapseR_zero {a y : ℝ} (ha : 0 ≤ a) :
      collapseR a y = 0 ↔ a = 0 ∧ |y| ≤ 1 := by
    unfold collapseR
    constructor
    · intro h
      have := le_max_left a (|y| - 1)
      have := le_max_right a (|y| - 1)
      constructor <;> linarith
    · rintro ⟨rfl, h⟩
      exact max_eq_left (by linarith)
  have collapseQ_pos_lt {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
      (hst : s < t) (ht : 0 < collapseR a t) : collapseQ a s < collapseQ a t := by
    have ht0 : 0 ≤ t := by linarith
    have hrs := collapseR_nonneg (y := s) ha
    have hrt := collapseR_nonneg (y := t) ha
    have hmono : collapseR a s ≤ collapseR a t := by
      unfold collapseR
      rw [abs_of_nonneg hs, abs_of_nonneg ht0]
      exact max_le_max_left a (by linarith)
    have hdenS : 0 < 1 + collapseR a s := by linarith
    have hdenT : 0 < 1 + collapseR a t := by linarith
    have hfrac : collapseR a s / (1 + collapseR a s) ≤
        collapseR a t / (1 + collapseR a t) := by
      apply (div_le_div_iff₀ hdenS hdenT).2
      nlinarith
    unfold collapseQ
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hfrac hs)
      (mul_lt_mul_of_pos_left hst (div_pos ht hdenT))
  have collapseQ_nonneg_fiber {a s t : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (h : collapseQ a s = collapseQ a t) :
      s = t ∨ (collapseR a s = 0 ∧ collapseR a t = 0) := by
    rcases lt_trichotomy s t with hst | hst | hst
    · right
      have hz : collapseR a t = 0 := by
        by_contra hn
        have hp : 0 < collapseR a t := lt_of_le_of_ne (collapseR_nonneg ha) (Ne.symm hn)
        exact (ne_of_lt (collapseQ_pos_lt ha hs hst hp)) h
      have hm : collapseR a s ≤ collapseR a t := by
        unfold collapseR
        rw [abs_of_nonneg hs, abs_of_nonneg ht]
        exact max_le_max_left a (by linarith)
      exact ⟨le_antisymm (by simpa [hz] using hm) (collapseR_nonneg ha), hz⟩
    · exact Or.inl hst
    · right
      have hz : collapseR a s = 0 := by
        by_contra hn
        have hp : 0 < collapseR a s := lt_of_le_of_ne (collapseR_nonneg ha) (Ne.symm hn)
        exact (ne_of_lt (collapseQ_pos_lt ha ht hst hp)) h.symm
      have hm : collapseR a t ≤ collapseR a s := by
        unfold collapseR
        rw [abs_of_nonneg hs, abs_of_nonneg ht]
        exact max_le_max_left a (by linarith)
      exact ⟨hz, le_antisymm (by simpa [hz] using hm) (collapseR_nonneg ha)⟩
  have collapseQ_fiber {a y z : ℝ} (ha : 0 ≤ a) (h : collapseQ a y = collapseQ a z) :
      y = z ∨ (a = 0 ∧ |y| ≤ 1 ∧ |z| ≤ 1) := by
    have habs : collapseQ a |y| = collapseQ a |z| := by
      rw [← collapseQ_abs ha, ← collapseQ_abs ha, h]
    rcases collapseQ_nonneg_fiber ha (abs_nonneg y) (abs_nonneg z) habs with hm | hm
    · have hr : collapseR a y = collapseR a z := by simp only [collapseR, hm]
      have hc : collapseR a y / (1 + collapseR a y) * y =
          collapseR a y / (1 + collapseR a y) * z := by simpa only [collapseQ, ← hr] using h
      rcases mul_eq_mul_left_iff.mp hc with he | he
      · exact Or.inl he
      · right
        have hy : collapseR a y = 0 := (div_eq_zero_iff).mp he |>.resolve_right (by
          have := collapseR_nonneg (y := y) ha
          linarith)
        have hz : collapseR a z = 0 := hr ▸ hy
        exact ⟨(collapseR_zero ha).mp hy |>.1, (collapseR_zero ha).mp hy |>.2,
          (collapseR_zero ha).mp hz |>.2⟩
    · right
      have hy : collapseR a y = 0 := by simpa only [collapseR, abs_abs] using hm.1
      have hz : collapseR a z = 0 := by simpa only [collapseR, abs_abs] using hm.2
      exact ⟨(collapseR_zero ha).mp hy |>.1, (collapseR_zero ha).mp hy |>.2,
        (collapseR_zero ha).mp hz |>.2⟩
  have collapseY_factor_pos (a : ℝ) : 0 < 1 + 1 / max a 1 := by
    have hb : 0 < max a 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    positivity
  have collapseY_fiber {a y z : ℝ} (ha : 0 ≤ a) (h : collapseY a y = collapseY a z) :
      y = z ∨ (a = 0 ∧ |y| ≤ 1 ∧ |z| ≤ 1) := by
    apply collapseQ_fiber ha
    exact (mul_left_cancel₀ (ne_of_gt (collapseY_factor_pos a))) h
  have collapseY_abs_le {a y : ℝ} (ha : 0 ≤ a) (hy : |y| ≤ 2) : |collapseY a y| ≤ |y| := by
    have hr := collapseR_nonneg (y := y) ha
    have hb : 0 < max a 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hd : 0 < 1 + collapseR a y := by linarith
    have hrb : collapseR a y ≤ max a 1 := by
      unfold collapseR
      exact max_le (le_max_left _ _) (le_trans (by linarith) (le_max_right _ _))
    have hc : (1 + 1 / max a 1) * (collapseR a y / (1 + collapseR a y)) ≤ 1 := by
      rw [one_add_div hb.ne', ← mul_div_assoc]
      apply (div_le_iff₀ hd).2
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hb).2
      nlinarith
    unfold collapseY collapseQ
    rw [← mul_assoc, abs_mul, abs_of_nonneg (mul_nonneg
      (le_of_lt (collapseY_factor_pos a)) (div_nonneg hr hd.le))]
    simpa using mul_le_mul_of_nonneg_right hc (abs_nonneg y)
  have collapseY_eq_self {a y : ℝ} (ha : 0 ≤ a) (hy : |y| ≤ 2)
      (h : a = 2 ∨ |y| = 2) : collapseY a y = y := by
    have hb : 0 < max a 1 := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
    have hrb : collapseR a y = max a 1 := by
      rcases h with rfl | h
      · unfold collapseR
        rw [max_eq_left (show |y| - 1 ≤ 2 by linarith), max_eq_left (by norm_num : (1:ℝ) ≤ 2)]
      · simp only [collapseR, h]
        norm_num
    unfold collapseY collapseQ
    rw [hrb]
    have hc : (1 + 1 / max a 1) * (max a 1 / (1 + max a 1)) = 1 := by
      field_simp
      ring
    calc
      _ = ((1 + 1 / max a 1) * (max a 1 / (1 + max a 1))) * y := by ring
      _ = y := by rw [hc, one_mul]
  have collapseY_zero {y : ℝ} (hy : |y| ≤ 1) : collapseY 0 y = 0 := by
    have hr : collapseR 0 y = 0 := (collapseR_zero (by norm_num)).2 ⟨rfl, hy⟩
    simp [collapseY, collapseQ, hr]
  have continuous_collapseY {a : ℝ} (ha : 0 ≤ a) : Continuous (collapseY a) := by
    have hr : Continuous (collapseR a) := continuous_const.max (continuous_abs.sub continuous_const)
    unfold collapseY collapseQ
    fun_prop (disch := intro y; have := collapseR_nonneg (y := y) ha; linarith)
  let D := Set.Icc (-2:ℝ) 2 × Set.Icc (-2:ℝ) 2
  have hy_mem (x y : Set.Icc (-2:ℝ) 2) : collapseY |x.val| y.val ∈ Set.Icc (-2:ℝ) 2 := by
    apply abs_le.mp
    exact (collapseY_abs_le (abs_nonneg x.val) (abs_le.mpr y.property)).trans (abs_le.mpr y.property)
  let f : D → D := fun v => (v.1, ⟨collapseY |v.1.val| v.2.val, hy_mem v.1 v.2⟩)
  have hx : Continuous (fun v : D => v.1.val) := continuous_subtype_val.comp continuous_fst
  have hy : Continuous (fun v : D => v.2.val) := continuous_subtype_val.comp continuous_snd
  have hr : Continuous (fun v : D => collapseR |v.1.val| v.2.val) :=
    hx.abs.max (hy.abs.sub continuous_const)
  have hc : Continuous (fun v : D => collapseY |v.1.val| v.2.val) := by
    unfold collapseY collapseQ
    have hb : Continuous (fun v : D => max |v.1.val| 1) := hx.abs.max continuous_const
    have hbn (v : D) : max |v.1.val| 1 ≠ 0 := by
      have := le_max_right |v.1.val| (1:ℝ)
      linarith
    have hdn (v : D) : 1 + collapseR |v.1.val| v.2.val ≠ 0 := by
      have := collapseR_nonneg (y := v.2.val) (abs_nonneg v.1.val)
      linarith
    exact (continuous_const.add (continuous_const.div hb hbn)).mul
      ((hr.div (continuous_const.add hr) hdn).mul hy)
  let F : C(D,D) := ⟨f, continuous_fst.prodMk (hc.subtype_mk _)⟩
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro v
    refine ⟨rfl, ?_⟩
    change (1 + 1 / max |v.1.val| 1) *
      (collapseR |v.1.val| v.2.val / (1 + collapseR |v.1.val| v.2.val) * v.2.val) = _
    unfold collapseR
    ring
  · intro w
    have hx0 := abs_nonneg w.1.val
    have hx2 : |w.1.val| ≤ 2 := abs_le.mpr w.1.property
    have hm : collapseY |w.1.val| (-2) = -2 :=
      collapseY_eq_self hx0 (by norm_num) (Or.inr (by norm_num))
    have hp : collapseY |w.1.val| 2 = 2 :=
      collapseY_eq_self hx0 (by norm_num) (Or.inr (by norm_num))
    have hi := intermediate_value_Icc (by norm_num : (-2:ℝ) ≤ 2)
      (continuous_collapseY hx0).continuousOn
    have hw : w.2.val ∈ Set.Icc (collapseY |w.1.val| (-2)) (collapseY |w.1.val| 2) := by
      rw [hm, hp]
      exact w.2.property
    obtain ⟨y, hym, hye⟩ := hi hw
    refine ⟨(w.1, ⟨y, hym⟩), ?_⟩
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact hye
  · intro v w
    constructor
    · intro h
      have he1 := congrArg (fun u : D => u.1.val) h
      change v.1.val = w.1.val at he1
      have he2 := congrArg (fun u : D => u.2.val) h
      change collapseY |v.1.val| v.2.val = collapseY |w.1.val| w.2.val at he2
      rw [← he1] at he2
      rcases collapseY_fiber (abs_nonneg v.1.val) he2 with he | he
      · left
        exact Prod.ext (Subtype.ext he1) (Subtype.ext he)
      · right
        have hxz : v.1.val = 0 := abs_eq_zero.mp he.1
        exact ⟨⟨hxz, he.2.1⟩, ⟨he1 ▸ hxz, he.2.2⟩⟩
    · rintro (rfl | ⟨hv, hw⟩)
      · rfl
      · apply Prod.ext
        · apply Subtype.ext
          exact hv.1.trans hw.1.symm
        · apply Subtype.ext
          change collapseY |v.1.val| v.2.val = collapseY |w.1.val| w.2.val
          rw [hv.1, hw.1, abs_zero, collapseY_zero hv.2, collapseY_zero hw.2]
  · intro v h
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change collapseY |v.1.val| v.2.val = v.2.val
      exact collapseY_eq_self (abs_nonneg v.1.val) (abs_le.mpr v.2.property) h
end AlternatingSphereCover
