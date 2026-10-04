import Mathlib

namespace CurveComplex.WeightedFlowScratch

/- Anonymous source-route probes. Cutting depth is expressed without division
by band width, so a zero-weight band does not create a discontinuity. These
are not yet named, reviewed declarations. -/

theorem bandClock_zero_width (depth start : ℝ) : min (0 : ℝ) (max 0 (depth - start)) = 0 := by
  simp

theorem bandClock_continuous {X : Type*} [TopologicalSpace X] (width depth start : X → ℝ)
    (hw : Continuous width) (hd : Continuous depth) (hs : Continuous start) :
    Continuous (fun x => min (width x) (max 0 (depth x - start x))) := by
  exact hw.min (continuous_const.max (hd.sub hs))

theorem bandClock_adjacent_split (a b depth start : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    min a (max 0 (depth - start)) +
        min b (max 0 (depth - (start + a))) =
      min (a + b) (max 0 (depth - start)) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

theorem bandClock_bounds (width depth start : ℝ) (hw : 0 ≤ width) :
    0 ≤ min width (max 0 (depth - start)) ∧
      min width (max 0 (depth - start)) ≤ width := by
  exact ⟨le_min hw (le_max_left _ _), min_le_left _ _⟩

theorem bandClock_before_start (width depth start : ℝ) (hw : 0 ≤ width) (hd : depth ≤ start) :
    min width (max 0 (depth - start)) = 0 := by
  rw [max_eq_left (sub_nonpos.mpr hd), min_eq_right hw]

theorem bandClock_after_end (width depth start : ℝ) (hw : 0 ≤ width)
    (hd : start + width ≤ depth) :
    min width (max 0 (depth - start)) = width := by
  rw [min_eq_left]
  exact le_trans (by linarith) (le_max_right _ _)

open scoped BigOperators

theorem bandClock_finite_prefix_sum (width : ℕ → ℝ) (hw : ∀ j, 0 ≤ width j) (depth : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n,
      min (width j) (max 0 (depth - ∑ k ∈ Finset.range j, width k))) =
      min (∑ j ∈ Finset.range n, width j) (max 0 depth) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hn : 0 ≤ ∑ j ∈ Finset.range n, width j :=
      Finset.sum_nonneg (fun j _ => hw j)
    simpa using bandClock_adjacent_split (∑ j ∈ Finset.range n, width j)
      (width n) depth 0 hn (hw n)


end CurveComplex.WeightedFlowScratch
