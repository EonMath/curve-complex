import Mathlib
import CurveComplexGenusTwo.Hyperbolic.Cayley
import CurveComplexGenusTwo.Hyperbolic.DensityBridge

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal UpperHalfPlane

private theorem circle_height_sq_pos (c r a b x : ℝ) (hr : 0 < r)
    (ha : c-r < a) (hb : b < c+r) (hx : x ∈ Icc a b) :
    0 < r^2-(x-c)^2 := by
  have hlo : -r < x-c := by linarith [hx.1]
  have hhi : x-c < r := by linarith [hx.2]
  nlinarith [mul_pos (sub_pos.mpr hhi) (by linarith : 0 < r+(x-c))]

private theorem circle_arcsin_deriv (c r x : ℝ) (hr : 0 < r)
    (hx : (x-c)^2 < r^2) :
    HasDerivAt (fun y => Real.arcsin ((y-c)/r))
      (Real.sqrt (r^2-(x-c)^2))⁻¹ x := by
  have ha : -1 < (x-c)/r := by
    apply (lt_div_iff₀ hr).mpr
    nlinarith
  have hb : (x-c)/r < 1 := by
    apply (div_lt_iff₀ hr).mpr
    nlinarith
  have h := (Real.hasDerivAt_arcsin (ne_of_gt ha) (ne_of_lt hb)).comp x
    (((hasDerivAt_id x).sub_const c).div_const r)
  have hq : 0 < r^2-(x-c)^2 := sub_pos.mpr hx
  have he : 1-((x-c)/r)^2 = (r^2-(x-c)^2)/r^2 := by
    field_simp
    <;> ring
  have hd : (Real.sqrt (1-((x-c)/r)^2))⁻¹ * ((1:ℝ)/r) =
      (Real.sqrt (r^2-(x-c)^2))⁻¹ := by
    rw [he,Real.sqrt_div hq.le,Real.sqrt_sq_eq_abs,abs_of_pos hr]
    field_simp [hr.ne', (Real.sqrt_pos.mpr hq).ne']
  convert h using 1
  · funext y; rfl
  · simpa only [one_div] using hd.symm

private theorem circle_reciprocal_height_integral (c r a b : ℝ)
    (hr : 0 < r) (hab : a ≤ b) (ha : c-r < a) (hb : b < c+r) :
    (∫ x : ℝ in a..b, (Real.sqrt (r^2-(x-c)^2))⁻¹) =
      Real.arcsin ((b-c)/r)-Real.arcsin ((a-c)/r) := by
  have hq : ∀ x ∈ Icc a b, 0 < r^2-(x-c)^2 :=
    fun x hx => circle_height_sq_pos c r a b x hr ha hb hx
  have hc : ContinuousOn (fun x : ℝ => (Real.sqrt (r^2-(x-c)^2))⁻¹) (Icc a b) := by
    apply ContinuousOn.inv₀
    · exact Real.continuous_sqrt.continuousOn.comp
        (continuous_const.sub ((continuous_id.sub continuous_const).pow 2)).continuousOn
        (mapsTo_univ _ _)
    · intro x hx; exact (Real.sqrt_pos.mpr (hq x hx)).ne'
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hab] at hx
    exact circle_arcsin_deriv c r x hr (by linarith [hq x hx])
  · exact hc.intervalIntegrable_of_Icc hab

private theorem vertical_density_integral (l u : ℝ) (hl : 0 < l) (hlu : l ≤ u) :
    (∫⁻ y : ℝ in Ioo l u, ENNReal.ofReal (y ^ (-2 : ℝ))) =
      ENNReal.ofReal (l⁻¹-u⁻¹) := by
  have hz : (0 : ℝ) ∉ uIcc l u := by
    rw [uIcc_of_le hlu]
    intro h
    linarith [h.1]
  have hi := intervalIntegral.intervalIntegrable_rpow (μ := volume)
    (r := (-2 : ℝ)) (Or.inr hz)
  have hii : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ioo l u) :=
    hi.1.mono Ioo_subset_Ioc_self le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hii]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hlu,
      integral_rpow (Or.inr ⟨by norm_num, hz⟩)]
    norm_num [Real.rpow_neg_one]
    congr 1
    ring
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact Real.rpow_nonneg (by linarith [hy.1]) _

private theorem lintegral_between_graphs
    (s : Set ℝ) (g h : ℝ → ℝ) (f : ℝ → ℝ≥0∞)
    (hs : MeasurableSet s) (hg : Measurable g) (hh : Measurable h) (hf : Measurable f) :
    (∫⁻ p : ℝ × ℝ in {p | p.1 ∈ s ∧ g p.1 < p.2 ∧ p.2 < h p.1}, f p.2) =
      ∫⁻ x : ℝ in s, ∫⁻ y : ℝ in Ioo (g x) (h x), f y := by
  have ht : MeasurableSet {p : ℝ × ℝ | p.1 ∈ s ∧ g p.1 < p.2 ∧ p.2 < h p.1} :=
    (hs.preimage measurable_fst).inter
      ((measurableSet_lt (hg.comp measurable_fst) measurable_snd).inter
       (measurableSet_lt measurable_snd (hh.comp measurable_fst)))
  rw [← lintegral_indicator ht, Measure.volume_eq_prod]
  rw [lintegral_prod _ (by fun_prop), ← lintegral_indicator hs]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ s
  · simp [Set.indicator, hx,
      ← lintegral_indicator (measurableSet_Ioo : MeasurableSet (Ioo (g x) (h x)))]
  · simp [Set.indicator, hx]

private theorem hyperbolic_density_eq_rpow {y : ℝ} (hy : 0 < y) :
    (↑((1 / ‖y‖₊) ^ 2 : NNReal) : ℝ≥0∞) =
      ENNReal.ofReal (y ^ (-2 : ℝ)) := by
  have hrpow : y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := by
    norm_num [Real.rpow_intCast]
  rw [hrpow, ENNReal.ofReal_inv_of_pos (pow_pos hy 2),
    ENNReal.ofReal_pow hy.le]
  rw [Real.nnnorm_of_nonneg hy.le]
  have hne : (NNReal.mk y hy.le) ≠ 0 := by
    exact NNReal.coe_ne_zero.mp (by simpa using hy.ne')
  rw [ENNReal.coe_pow, ENNReal.coe_div hne,
    ENNReal.ofReal_eq_coe_nnreal hy.le]
  simp only [div_eq_mul_inv, ENNReal.coe_one, one_mul,
    ENNReal.inv_pow]

private theorem upper_volume_coordinates (s : Set UpperHalfPlane) (hs : MeasurableSet s) :
    volume s = ∫⁻ p : ℝ × ℝ in
      (fun z : UpperHalfPlane => ((z : ℂ).re, (z : ℂ).im)) '' s,
      ENNReal.ofReal (p.2 ^ (-2 : ℝ)) := by
  rw [UpperHalfPlane.volume_eq_lintegral]
  have hi : MeasurableSet ((UpperHalfPlane.coe) '' s) :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs
  calc
    _ = ∫⁻ z : ℂ in (UpperHalfPlane.coe) '' s,
        ENNReal.ofReal (z.im ^ (-2 : ℝ)) := by
      apply setLIntegral_congr_fun hi
      rintro z ⟨w, hw, rfl⟩
      exact hyperbolic_density_eq_rpow w.im_pos
    _ = _ := by
      simpa only [Set.image_image, Function.comp_def,
        Complex.measurableEquivRealProd_apply] using
        Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_emb
          Complex.measurableEquivRealProd.measurableEmbedding
          (fun p : ℝ × ℝ => ENNReal.ofReal (p.2 ^ (-2 : ℝ)))
          ((UpperHalfPlane.coe) '' s)

theorem compact_circle_strip_normalized_area
    (c₀ c₁ r₀ r₁ a b : ℝ)
    (hr₀ : 0 < r₀) (hr₁ : 0 < r₁) (hab : a ≤ b)
    (ha₀ : c₀ - r₀ < a) (hb₀ : b < c₀ + r₀)
    (ha₁ : c₁ - r₁ < a) (hb₁ : b < c₁ + r₁)
    (horder : ∀ x ∈ Set.Ioo a b,
      Real.sqrt (r₀ ^ 2 - (x - c₀) ^ 2) ≤
      Real.sqrt (r₁ ^ 2 - (x - c₁) ^ 2)) :
    (μHE[2] : Measure H2)
      {z | a < z.re ∧ z.re < b ∧
        Real.sqrt (r₀ ^ 2 - (z.re - c₀) ^ 2) < z.im ∧
        z.im < Real.sqrt (r₁ ^ 2 - (z.re - c₁) ^ 2)} =
      ENNReal.ofReal
        ((Real.arcsin ((b - c₀) / r₀) - Real.arcsin ((a - c₀) / r₀)) -
         (Real.arcsin ((b - c₁) / r₁) - Real.arcsin ((a - c₁) / r₁))) := by
  let L : ℝ → ℝ := fun x => Real.sqrt (r₀^2-(x-c₀)^2)
  let U : ℝ → ℝ := fun x => Real.sqrt (r₁^2-(x-c₁)^2)
  have hLc : Continuous L := by dsimp [L]; fun_prop
  have hUc : Continuous U := by dsimp [U]; fun_prop
  have hLp : ∀ x ∈ Icc a b, 0 < L x := fun x hx =>
    Real.sqrt_pos.mpr (circle_height_sq_pos c₀ r₀ a b x hr₀ ha₀ hb₀ hx)
  have hUp : ∀ x ∈ Icc a b, 0 < U x := fun x hx =>
    Real.sqrt_pos.mpr (circle_height_sq_pos c₁ r₁ a b x hr₁ ha₁ hb₁ hx)
  let S : Set UpperHalfPlane := {z | a < z.re ∧ z.re < b ∧ L z.re < z.im ∧ z.im < U z.re}
  have hS : MeasurableSet S := by
    dsimp [S]
    exact (measurableSet_lt measurable_const UpperHalfPlane.continuous_re.measurable).inter
      ((measurableSet_lt UpperHalfPlane.continuous_re.measurable measurable_const).inter
      ((measurableSet_lt (hLc.comp UpperHalfPlane.continuous_re).measurable
        UpperHalfPlane.continuous_im.measurable).inter
       (measurableSet_lt UpperHalfPlane.continuous_im.measurable
        (hUc.comp UpperHalfPlane.continuous_re).measurable)))
  have himage : (fun z : UpperHalfPlane => ((z : ℂ).re, (z : ℂ).im)) '' S =
      {p : ℝ × ℝ | p.1 ∈ Ioo a b ∧ L p.1 < p.2 ∧ p.2 < U p.1} := by
    ext p
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨⟨hz.1,hz.2.1⟩,hz.2.2⟩
    · rintro ⟨hx, hy⟩
      have hp : 0 < p.2 := lt_trans (hLp p.1 ⟨hx.1.le,hx.2.le⟩) hy.1
      refine ⟨⟨⟨p.1,p.2⟩,hp⟩, ?_, ?_⟩
      · exact ⟨hx.1,hx.2,hy⟩
      · rfl
  change (μHE[2] : Measure UpperHalfPlane) S = _
  rw [normalizedHausdorff_eq_upperHalfPlane_volume, upper_volume_coordinates S hS,
    himage, lintegral_between_graphs (Ioo a b) L U
      (fun y : ℝ => ENNReal.ofReal (y ^ (-2 : ℝ))) measurableSet_Ioo
      hLc.measurable hUc.measurable (by fun_prop)]
  have hv : (∫⁻ x : ℝ in Ioo a b, ∫⁻ y : ℝ in Ioo (L x) (U x),
      ENNReal.ofReal (y ^ (-2 : ℝ))) =
      ∫⁻ x : ℝ in Ioo a b, ENNReal.ofReal ((L x)⁻¹-(U x)⁻¹) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro x hx
    exact vertical_density_integral (L x) (U x)
      (hLp x ⟨hx.1.le,hx.2.le⟩) (horder x hx)
  rw [hv]
  have hLi : IntervalIntegrable (fun x => (L x)⁻¹) volume a b :=
    (hLc.continuousOn.inv₀ (fun x hx => (hLp x hx).ne')).intervalIntegrable_of_Icc hab
  have hUi : IntervalIntegrable (fun x => (U x)⁻¹) volume a b :=
    (hUc.continuousOn.inv₀ (fun x hx => (hUp x hx).ne')).intervalIntegrable_of_Icc hab
  have hi : IntegrableOn (fun x => (L x)⁻¹-(U x)⁻¹) (Ioo a b) :=
    (hLi.sub hUi).1.mono Ioo_subset_Ioc_self le_rfl
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_sub hLi hUi]
    rw [circle_reciprocal_height_integral c₀ r₀ a b hr₀ hab ha₀ hb₀,
      circle_reciprocal_height_integral c₁ r₁ a b hr₁ hab ha₁ hb₁]
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact sub_nonneg.mpr (inv_le_inv₀ (hUp x ⟨hx.1.le,hx.2.le⟩)
      (hLp x ⟨hx.1.le,hx.2.le⟩) |>.mpr (horder x hx))
end CurveComplex.Hyperbolic
