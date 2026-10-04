import Mathlib

open Filter Topology

namespace CurveComplex.Hyperbolic

/-- An explicit lower approximation to `arsinh` that is sharp at zero. -/
theorem arsinh_lower_rational {t : ℝ} (ht : 0 ≤ t) :
    2 * t / (t + 2) ≤ Real.arsinh t := by
  have hlog : Real.log (1 + t) ≤ Real.arsinh t := by
    rw [Real.arsinh]
    apply Real.log_le_log (by positivity)
    have hsqrt : 1 ≤ Real.sqrt (1 + t ^ 2) := by
      apply Real.le_sqrt (by norm_num) (by positivity) |>.2
      nlinarith [sq_nonneg t]
    linarith
  exact (Real.le_log_one_add_of_nonneg ht).trans hlog

/-- The slope lower bound tends to one as a neighborhood shrinks. -/
theorem arsinh_lower_on_interval {t δ : ℝ} (ht : 0 ≤ t)
    (htδ : t ≤ δ) :
    (2 / (δ + 2)) * t ≤ Real.arsinh t := by
  have hδ : 0 ≤ δ := ht.trans htδ
  have hden : 0 < t + 2 := by linarith
  have hdenδ : 0 < δ + 2 := by linarith
  calc
    (2 / (δ + 2)) * t = 2 * t / (δ + 2) := by ring
    _ ≤ 2 * t / (t + 2) := by
      apply (div_le_div_iff₀ hdenδ hden).2
      nlinarith
    _ ≤ Real.arsinh t := arsinh_lower_rational ht

/-- The lower half of a quantitative local comparison, assuming an upper
height bound and an upper bound on the Poincaré chord ratio. -/
theorem upperHalfPlane_dist_lower_of_ratio_bound
    (z w : UpperHalfPlane) {C δ : ℝ} (hC : 0 < C)
    (hzC : z.im ≤ C) (hwC : w.im ≤ C)
    (hδ : 0 ≤ δ)
    (hratio : dist (z : ℂ) w /
        (2 * Real.sqrt (z.im * w.im)) ≤ δ) :
    (2 / (δ + 2)) * (dist (z : ℂ) w / C) ≤ dist z w := by
  let q := dist (z : ℂ) w / (2 * Real.sqrt (z.im * w.im))
  have hq : 0 ≤ q := by positivity
  have hsqrt : Real.sqrt (z.im * w.im) ≤ C := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hC.le
    · have hprod : z.im * w.im ≤ C * C :=
        mul_le_mul hzC hwC w.im_pos.le hC.le
      nlinarith
  have hpos : 0 < Real.sqrt (z.im * w.im) := by positivity
  have hqlo : dist (z : ℂ) w / (2 * C) ≤ q := by
    dsimp [q]
    gcongr
  have hcoef : 0 ≤ 2 / (δ + 2) := by positivity
  calc
    (2 / (δ + 2)) * (dist (z : ℂ) w / C) =
        2 * ((2 / (δ + 2)) * (dist (z : ℂ) w / (2 * C))) := by ring
    _ ≤ 2 * ((2 / (δ + 2)) * q) := by gcongr
    _ ≤ 2 * Real.arsinh q := by
      gcongr
      exact arsinh_lower_on_interval hq hratio
    _ = dist z w := (UpperHalfPlane.dist_eq z w).symm

/-- Explicit lower distance bound on a finite-height region of Euclidean
diameter at most `D`. Its coefficient converges to `1/C` as `D → 0`. -/
theorem upperHalfPlane_dist_lower_on_height_band
    (z w : UpperHalfPlane) {c C D : ℝ}
    (hc : 0 < c) (hC : 0 < C) (hD : 0 ≤ D)
    (hzc : c ≤ z.im) (hwc : c ≤ w.im)
    (hzC : z.im ≤ C) (hwC : w.im ≤ C)
    (hdiam : dist (z : ℂ) w ≤ D) :
    (2 / (D / (2 * c) + 2)) * (dist (z : ℂ) w / C) ≤ dist z w := by
  have hsqrt : c ≤ Real.sqrt (z.im * w.im) := by
    apply (Real.le_sqrt hc.le (mul_nonneg z.im_pos.le w.im_pos.le)).2
    have hprod : c * c ≤ z.im * w.im :=
      mul_le_mul hzc hwc hc.le z.im_pos.le
    nlinarith
  have hratio : dist (z : ℂ) w / (2 * Real.sqrt (z.im * w.im)) ≤
      D / (2 * c) := by
    gcongr
  exact upperHalfPlane_dist_lower_of_ratio_bound z w hC hzC hwC
    (by positivity) hratio

private theorem abs_im_sub_le_dist (z w : UpperHalfPlane) :
    |z.im - w.im| ≤ dist (z : ℂ) w := by
  simpa [Complex.sub_im, dist_eq_norm] using
    Complex.abs_im_le_norm ((z : ℂ) - (w : ℂ))

/-- A shrinking Euclidean neighborhood has hyperbolic distance trapped
between two explicit multiples of Euclidean distance. -/
theorem upperHalfPlane_local_dist_squeeze
    (z₀ z w : UpperHalfPlane) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im)
    (hz : dist (z : ℂ) z₀ ≤ r)
    (hw : dist (w : ℂ) z₀ ≤ r) :
    (2 / ((2 * r) / (2 * (z₀.im - r)) + 2)) *
        (dist (z : ℂ) w / (z₀.im + r)) ≤ dist z w ∧
      dist z w ≤ dist (z : ℂ) w / (z₀.im - r) := by
  have hzi := abs_im_sub_le_dist z z₀
  have hwi := abs_im_sub_le_dist w z₀
  have hzc : z₀.im - r ≤ z.im := by
    have := (abs_le.mp hzi).1
    linarith
  have hwc : z₀.im - r ≤ w.im := by
    have := (abs_le.mp hwi).1
    linarith
  have hzC : z.im ≤ z₀.im + r := by
    have := (abs_le.mp hzi).2
    linarith
  have hwC : w.im ≤ z₀.im + r := by
    have := (abs_le.mp hwi).2
    linarith
  have hdiam : dist (z : ℂ) w ≤ 2 * r := by
    calc
      dist (z : ℂ) w ≤ dist (z : ℂ) z₀ + dist (z₀ : ℂ) w := dist_triangle _ _ _
      _ ≤ r + r := by simpa [dist_comm] using add_le_add hz hw
      _ = 2 * r := by ring
  constructor
  · exact upperHalfPlane_dist_lower_on_height_band z w
      (by linarith : 0 < z₀.im - r) (by linarith : 0 < z₀.im + r)
      (by linarith : 0 ≤ 2 * r) hzc hwc hzC hwC hdiam
  · exact (UpperHalfPlane.dist_le_dist_coe_div_sqrt z w).trans (by
      have hsqrt : z₀.im - r ≤ Real.sqrt (z.im * w.im) := by
        apply (Real.le_sqrt (by linarith)
          (mul_nonneg z.im_pos.le w.im_pos.le)).2
        have hprod : (z₀.im - r) * (z₀.im - r) ≤ z.im * w.im :=
          mul_le_mul hzc hwc (by linarith) z.im_pos.le
        nlinarith
      gcongr)

noncomputable def localLowerSlope (z₀ : UpperHalfPlane) (r : ℝ) : ℝ :=
  (2 / ((2 * r) / (2 * (z₀.im - r)) + 2)) / (z₀.im + r)

noncomputable def localUpperSlope (z₀ : UpperHalfPlane) (r : ℝ) : ℝ :=
  1 / (z₀.im - r)

theorem localLowerSlope_tendsto (z₀ : UpperHalfPlane) :
    Filter.Tendsto (localLowerSlope z₀) (nhds (0 : ℝ))
      (nhds (1 / z₀.im)) := by
  have hcont : ContinuousAt (localLowerSlope z₀) 0 := by
    unfold localLowerSlope
    fun_prop (disch := simp [ne_of_gt z₀.im_pos])
  convert hcont.tendsto using 1
  simp [localLowerSlope]

theorem localUpperSlope_tendsto (z₀ : UpperHalfPlane) :
    Filter.Tendsto (localUpperSlope z₀) (nhds (0 : ℝ))
      (nhds (1 / z₀.im)) := by
  have hcont : ContinuousAt (localUpperSlope z₀) 0 := by
    unfold localUpperSlope
    fun_prop (disch := simp [ne_of_gt z₀.im_pos])
  convert hcont.tendsto using 1
  simp [localUpperSlope]

theorem upperHalfPlane_local_dist_squeeze_slopes
    (z₀ z w : UpperHalfPlane) {r : ℝ}
    (hr : 0 ≤ r) (hrsmall : r < z₀.im)
    (hz : dist (z : ℂ) z₀ ≤ r)
    (hw : dist (w : ℂ) z₀ ≤ r) :
    localLowerSlope z₀ r * dist (z : ℂ) w ≤ dist z w ∧
      dist z w ≤ localUpperSlope z₀ r * dist (z : ℂ) w := by
  have h := upperHalfPlane_local_dist_squeeze z₀ z w hr hrsmall hz hw
  simpa [localLowerSlope, localUpperSlope, div_eq_mul_inv,
    mul_assoc, mul_left_comm, mul_comm] using h

/-- The exact pointwise metric density of the Poincaré distance in the
complex coordinate chart. -/
theorem upperHalfPlane_dist_ratio_tendsto (z₀ : UpperHalfPlane) :
    Tendsto (fun w : UpperHalfPlane => dist z₀ w / dist (z₀ : ℂ) w)
      (𝓝[≠] z₀) (𝓝 (1 / z₀.im)) := by
  have hrad : Tendsto (fun w : UpperHalfPlane => dist (w : ℂ) z₀)
      (𝓝[≠] z₀) (𝓝 0) := by
    have hcont : ContinuousAt (fun w : UpperHalfPlane => dist (w : ℂ) z₀) z₀ := by
      fun_prop
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hsmall : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z₀,
      dist (w : ℂ) z₀ < z₀.im :=
    hrad.eventually (Iio_mem_nhds z₀.im_pos)
  have hne : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z₀, w ≠ z₀ := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    simpa using hw
  have hlo : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z₀,
      localLowerSlope z₀ (dist (w : ℂ) z₀) ≤
        dist z₀ w / dist (z₀ : ℂ) w := by
    filter_upwards [hsmall, hne] with w hsw hnw
    have hs := (upperHalfPlane_local_dist_squeeze_slopes z₀ z₀ w
      (dist_nonneg) hsw (by simp) le_rfl).1
    have hE : 0 < dist (z₀ : ℂ) w := by
      apply dist_pos.mpr
      exact fun he => hnw (UpperHalfPlane.coe_injective he).symm
    exact (le_div_iff₀ hE).2 (by simpa [dist_comm (w : ℂ) z₀] using hs)
  have hhi : ∀ᶠ w : UpperHalfPlane in 𝓝[≠] z₀,
      dist z₀ w / dist (z₀ : ℂ) w ≤
        localUpperSlope z₀ (dist (w : ℂ) z₀) := by
    filter_upwards [hsmall, hne] with w hsw hnw
    have hs := (upperHalfPlane_local_dist_squeeze_slopes z₀ z₀ w
      (dist_nonneg) hsw (by simp) le_rfl).2
    have hE : 0 < dist (z₀ : ℂ) w := by
      apply dist_pos.mpr
      exact fun he => hnw (UpperHalfPlane.coe_injective he).symm
    exact (div_le_iff₀ hE).2 (by simpa [dist_comm (w : ℂ) z₀] using hs)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    ((localLowerSlope_tendsto z₀).comp hrad)
    ((localUpperSlope_tendsto z₀).comp hrad) hlo hhi

end CurveComplex.Hyperbolic
