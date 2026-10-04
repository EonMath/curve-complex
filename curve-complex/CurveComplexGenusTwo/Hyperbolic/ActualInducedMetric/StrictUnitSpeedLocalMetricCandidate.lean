import Mathlib

namespace CurveComplex.Hyperbolic
open Set Topology ContinuousLinearMap
open scoped NNReal

theorem strict_unit_speed_local_metric_bounds {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : ℝ → F} {v : F} {x : ℝ}
    (hf : HasStrictDerivAt f v x) (hv : ‖v‖ = 1)
    (ε : ℝ≥0) (hε : 0 < ε) (hεone : ε < 1) :
    ∃ U : Set ℝ, IsOpen U ∧ x ∈ U ∧
      LipschitzWith (1 + ε) (U.domRestrict f) ∧
      AntilipschitzWith (1 - ε)⁻¹ (U.domRestrict f) := by
  obtain ⟨s, hs, ha⟩ := hf.hasStrictFDerivAt.approximates_deriv_on_nhds (Or.inr hε)
  obtain ⟨U, hUs, hU, hxU⟩ := mem_nhds_iff.mp hs
  have happrox := ha.mono_set hUs
  have hnorm (y z : ℝ) : ‖(toSpanSingleton ℝ v) (y - z)‖ = dist y z := by
    simp [toSpanSingleton_apply, norm_smul, hv, Real.dist_eq]
  have herror (y : U) (z : U) :
      ‖f y - f z - (toSpanSingleton ℝ v) (y.val - z.val)‖ ≤ (ε : ℝ) * dist y.val z.val := by
    simpa only [Real.dist_eq, Real.norm_eq_abs] using happrox y y.property z z.property
  refine ⟨U, hU, hxU, LipschitzWith.of_dist_le_mul ?_, AntilipschitzWith.of_le_mul_dist ?_⟩
  · intro y z
    change dist (f y) (f z) ≤ (↑(1 + ε) : ℝ) * dist y.val z.val
    have h := norm_le_insert ((toSpanSingleton ℝ v) (y.val-z.val)) (f y - f z)
    rw [hnorm, norm_sub_rev ((toSpanSingleton ℝ v) (y.val-z.val))] at h
    rw [dist_eq_norm]
    simp only [NNReal.coe_add, NNReal.coe_one]
    nlinarith [herror y z]
  · intro y z
    change dist y.val z.val ≤ (↑((1 - ε)⁻¹) : ℝ) * dist (f y) (f z)
    have hepos : (0 : ℝ) < 1 - ε := by
      have he : (ε : ℝ) < 1 := by exact_mod_cast hεone
      linarith
    have h := norm_le_insert (f y - f z) ((toSpanSingleton ℝ v) (y.val-z.val))
    rw [hnorm, ← dist_eq_norm] at h
    have hl : (1 - (ε : ℝ)) * dist y.val z.val ≤ dist (f y) (f z) := by
      nlinarith [herror y z]
    rw [NNReal.coe_inv, NNReal.coe_sub (le_of_lt hεone), NNReal.coe_one]
    exact (le_inv_mul_iff₀ hepos).mpr hl

end CurveComplex.Hyperbolic
