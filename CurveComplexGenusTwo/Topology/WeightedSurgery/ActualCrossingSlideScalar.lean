import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic

namespace CurveComplex.ActualCrossingSlide
open Set
noncomputable section

def tent (x : ℝ) : ℝ := max 0 (1 - |x|)
def scalar (a x : ℝ) : ℝ := x + a * tent x

theorem tent_nonneg (x : ℝ) : 0 ≤ tent x := le_max_left _ _
theorem tent_le_one (x : ℝ) : tent x ≤ 1 := max_le (by norm_num) (by linarith [abs_nonneg x])
theorem tent_continuous : Continuous tent := by unfold tent; fun_prop

theorem scalar_fixed (a x : ℝ) (hx : 1 ≤ |x|) : scalar a x = x := by
  simp [scalar, tent, max_eq_left (by linarith : 1 - |x| ≤ 0)]

theorem scalar_continuous : Continuous (fun z : ℝ × ℝ => scalar z.1 z.2) := by
  unfold scalar
  exact continuous_snd.add (continuous_fst.mul (tent_continuous.comp continuous_snd))

theorem scalar_surjective (a : ℝ) : Function.Surjective (scalar a) := by
  intro y
  by_cases hy : 1 ≤ |y|
  · exact ⟨y, scalar_fixed a y hy⟩
  · have hc : Continuous (scalar a) := scalar_continuous.comp (continuous_const.prodMk continuous_id)
    have hleft : scalar a (-1) = -1 := scalar_fixed a (-1) (by norm_num)
    have hright : scalar a 1 = 1 := scalar_fixed a 1 (by norm_num)
    have hyI : y ∈ Icc (scalar a (-1)) (scalar a 1) := by
      rw [hleft, hright]
      have hya := abs_lt.mp (lt_of_not_ge hy)
      exact ⟨hya.1.le, hya.2.le⟩
    obtain ⟨x, _, hx⟩ := intermediate_value_Icc (by norm_num : (-1 : ℝ) ≤ 1) hc.continuousOn hyI
    exact ⟨x, hx⟩

def scalarInverse (a x : ℝ) : ℝ :=
  if x ≤ -1 then x else if x ≤ a then (x-a)/(1+a)
    else if x ≤ 1 then (x-a)/(1-a) else x

theorem scalarInverse_left (a : ℝ) (ha : |a| < 1) :
    Function.LeftInverse (scalarInverse a) (scalar a) := by
  have hal : -1 < a := (abs_lt.mp ha).1
  have har : a < 1 := (abs_lt.mp ha).2
  have hp : 0 < 1+a := by linarith
  have hn : 0 < 1-a := by linarith
  intro x
  by_cases hxl : x ≤ -1
  · have hf : scalar a x = x := scalar_fixed a x (by rw [abs_of_nonpos (by linarith)]; linarith)
    simp [scalarInverse, hf, hxl]
  · by_cases hx0 : x ≤ 0
    · have he : scalar a x = (1+a)*x+a := by
        rw [scalar, tent, abs_of_nonpos hx0, max_eq_right (by linarith)]
        ring
      have hv : -1 < scalar a x := by rw [he]; nlinarith
      have hv' : scalar a x ≤ a := by rw [he]; nlinarith
      unfold scalarInverse
      rw [ite_eq_right (not_le.mpr hv), ite_eq_left hv', he]
      field_simp [ne_of_gt hp]
      nlinarith
    · by_cases hxr : x ≤ 1
      · have he : scalar a x = (1-a)*x+a := by
          rw [scalar, tent, abs_of_nonneg (by linarith), max_eq_right (by linarith)]
          ring
        have hv : a < scalar a x := by rw [he]; nlinarith
        have hv0 : -1 < scalar a x := hal.trans hv
        have hv1 : scalar a x ≤ 1 := by rw [he]; nlinarith
        unfold scalarInverse
        rw [ite_eq_right (not_le.mpr hv0), ite_eq_right (not_le.mpr hv), ite_eq_left hv1, he]
        field_simp [ne_of_gt hn]
        nlinarith
      · have hf : scalar a x = x := scalar_fixed a x (by rw [abs_of_nonneg (by linarith)]; linarith)
        have hxa : ¬ x ≤ a := by linarith
        simp [scalarInverse, hf, hxl, hxa, hxr]

theorem scalarInverse_right (a : ℝ) (ha : |a| < 1) :
    Function.RightInverse (scalarInverse a) (scalar a) :=
  (scalarInverse_left a ha).rightInverse_of_surjective (scalar_surjective a)

abbrev Amount := {a : ℝ // |a| < 1}

theorem scalarInverse_continuous :
    Continuous (fun z : Amount × ℝ => scalarInverse z.1.val z.2) := by
  have hplus : ∀ z : Amount × ℝ, 1 + z.1.val ≠ 0 := by
    intro z
    have h := (abs_lt.mp z.1.property).1
    linarith
  have hminus : ∀ z : Amount × ℝ, 1 - z.1.val ≠ 0 := by
    intro z
    have h := (abs_lt.mp z.1.property).2
    linarith
  have hcplus : Continuous (fun z : Amount × ℝ => (z.2-z.1.val)/(1+z.1.val)) := by
    fun_prop (disch := exact hplus _)
  have hcminus : Continuous (fun z : Amount × ℝ => (z.2-z.1.val)/(1-z.1.val)) := by
    fun_prop (disch := exact hminus _)
  have hinner : Continuous (fun z : Amount × ℝ =>
      if z.2 ≤ 1 then (z.2-z.1.val)/(1-z.1.val) else z.2) := by
    apply continuous_if_le continuous_snd continuous_const hcminus.continuousOn continuous_snd.continuousOn
    intro z hz
    rw [hz, div_self (hminus z)]
  have hmid : Continuous (fun z : Amount × ℝ =>
      if z.2 ≤ z.1.val then (z.2-z.1.val)/(1+z.1.val)
      else if z.2 ≤ 1 then (z.2-z.1.val)/(1-z.1.val) else z.2) := by
    apply continuous_if_le continuous_snd (continuous_subtype_val.comp continuous_fst) hcplus.continuousOn hinner.continuousOn
    intro z hz
    change z.2 = z.1.val at hz
    have hz1 : z.2 ≤ 1 := by rw [hz]; exact (abs_lt.mp z.1.property).2.le
    rw [ite_eq_left hz1, hz]
    simp only [sub_self, zero_div]
  unfold scalarInverse
  apply continuous_if_le continuous_snd continuous_const continuous_snd.continuousOn hmid.continuousOn
  intro z hz
  have hza : z.2 ≤ z.1.val := by rw [hz]; exact (abs_lt.mp z.1.property).1.le
  rw [ite_eq_left hza, hz]
  field_simp [hplus z]
  ring

end
end CurveComplex.ActualCrossingSlide
