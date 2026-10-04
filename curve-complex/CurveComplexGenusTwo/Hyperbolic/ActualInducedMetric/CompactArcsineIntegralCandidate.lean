import Mathlib

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped Interval

theorem compact_arcsine_reciprocal_sqrt_integral {a b : ℝ}
    (ha : -1 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ x : ℝ in a..b, (Real.sqrt (1 - x ^ 2))⁻¹) =
      Real.arcsin b - Real.arcsin a := by
  have hpos : ∀ x ∈ Icc a b, 0 < 1 - x ^ 2 := by
    intro x hx
    have hm : -1 < x := ha.trans_le hx.1
    have hp : x < 1 := hx.2.trans_lt hb
    nlinarith
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt (1 - x ^ 2))⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀
    · exact Real.continuous_sqrt.continuousOn.comp
        (continuous_const.sub (continuous_id.pow 2)).continuousOn (mapsTo_univ _ _)
    · intro x hx; exact (Real.sqrt_pos.mpr (hpos x hx)).ne'
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    have hm : x ≠ -1 := ne_of_gt (ha.trans_le hx.1)
    have hp : x ≠ 1 := ne_of_lt (hx.2.trans_lt hb)
    simpa only [one_div] using Real.hasDerivAt_arcsin hm hp
  · exact hc.intervalIntegrable_of_Icc hab

end CurveComplex.Hyperbolic
