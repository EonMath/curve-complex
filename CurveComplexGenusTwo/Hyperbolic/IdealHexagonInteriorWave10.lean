import CurveComplexGenusTwo.Hyperbolic.DensityBridge
import CurveComplexGenusTwo.Hyperbolic.HexagonCoordinates
import Mathlib.Analysis.SpecialFunctions.PolarCoord

namespace CurveComplex.Hyperbolic

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Euclidean center of the circle orthogonal to the unit circle through
two adjacent ideal vertices. -/
noncomputable def idealHexagonSideCenter (i : Fin 6) : ℂ :=
  (2 / 3 : ℝ) * (idealHexagonVertex i + idealHexagonVertex (i + 1))

/-- The signed equation of an ideal side; the origin has positive sign. -/
noncomputable def idealHexagonSideEquation (i : Fin 6) (w : ℂ) : ℝ :=
  Complex.normSq w - 2 * (star (idealHexagonSideCenter i) * w).re + 1

theorem idealHexagonSideCenter_normSq (i : Fin 6) :
    Complex.normSq (idealHexagonSideCenter i) = 4 / 3 := by
  have hsq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;>
    simp [idealHexagonSideCenter, idealHexagonVertex,
      Complex.normSq_apply, Complex.mul_re, Complex.add_re,
      Complex.add_im] <;>
    nlinarith [hsq]

theorem idealHexagonSideCenter_injective :
    Function.Injective idealHexagonSideCenter := by
  intro i j h
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  fin_cases i <;> fin_cases j <;>
    simp [idealHexagonSideCenter, idealHexagonVertex,
      Complex.ext_iff, Complex.add_re, Complex.add_im] at h ⊢ <;>
    nlinarith [hs]

theorem idealHexagonSideEquation_eq_circle (i : Fin 6) (w : ℂ) :
    idealHexagonSideEquation i w =
      Complex.normSq (w - idealHexagonSideCenter i) - 1 / 3 := by
  rw [Complex.normSq_sub, idealHexagonSideCenter_normSq]
  simp [idealHexagonSideEquation, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  ring

theorem idealHexagonSideEquation_left_vertex (i : Fin 6) :
    idealHexagonSideEquation i (idealHexagonVertex i) = 0 := by
  have hsq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;>
    simp [idealHexagonSideEquation, idealHexagonSideCenter,
      idealHexagonVertex, Complex.normSq_apply, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im] <;>
    nlinarith [hsq]

theorem idealHexagonSideEquation_right_vertex (i : Fin 6) :
    idealHexagonSideEquation i (idealHexagonVertex (i + 1)) = 0 := by
  have hsq : (Real.sqrt 3) ^ 2 = 3 := by norm_num
  fin_cases i <;>
    simp [idealHexagonSideEquation, idealHexagonSideCenter,
      idealHexagonVertex, Complex.normSq_apply, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.add_re,
      Complex.add_im] <;>
    nlinarith [hsq]

theorem idealHexagonSideEquation_zero (i : Fin 6) :
    idealHexagonSideEquation i 0 = 1 := by
  simp [idealHexagonSideEquation]

theorem idealHexagonSideEquation_continuous (i : Fin 6) :
    Continuous (idealHexagonSideEquation i) := by
  unfold idealHexagonSideEquation
  fun_prop

/-- The open side of the geodesic circle containing the origin. -/
noncomputable def idealHexagonInwardHalfplane (i : Fin 6) : Set ℂ :=
  {w | 0 < idealHexagonSideEquation i w}

theorem idealHexagonInwardHalfplane_isOpen (i : Fin 6) :
    IsOpen (idealHexagonInwardHalfplane i) := by
  exact isOpen_Ioi.preimage (idealHexagonSideEquation_continuous i)

/-- The ideal hexagon interior in the Poincaré disc. -/
noncomputable def idealHexagonDiscInterior : Set ℂ :=
  Metric.ball (0 : ℂ) 1 ∩ ⋂ i : Fin 6, idealHexagonInwardHalfplane i

theorem idealHexagonDiscInterior_isOpen : IsOpen idealHexagonDiscInterior := by
  exact Metric.isOpen_ball.inter
    (isOpen_iInter_of_finite idealHexagonInwardHalfplane_isOpen)

/-- The same six-sided region in the upper half-plane, via Cayley. -/
noncomputable def idealHexagonInterior : Set UpperHalfPlane :=
  {z | (cayley z : ℂ) ∈ idealHexagonDiscInterior}

theorem idealHexagonInterior_isOpen : IsOpen idealHexagonInterior := by
  exact idealHexagonDiscInterior_isOpen.preimage
    (continuous_subtype_val.comp cayley_continuous)

theorem idealHexagonInterior_measurable : MeasurableSet idealHexagonInterior :=
  idealHexagonInterior_isOpen.measurableSet

theorem idealHexagonInterior_center_mem :
    UpperHalfPlane.I ∈ idealHexagonInterior := by
  change (cayley UpperHalfPlane.I : ℂ) ∈ idealHexagonDiscInterior
  have hc : (cayley UpperHalfPlane.I : ℂ) = 0 := by
    norm_num [cayley, UpperHalfPlane.I]
  rw [hc]
  refine ⟨by norm_num, Set.mem_iInter.mpr ?_⟩
  intro i
  simpa [idealHexagonInwardHalfplane] using
    (show 0 < idealHexagonSideEquation i 0 by
      rw [idealHexagonSideEquation_zero]
      norm_num)

/-- Angular projection of a side-circle center onto a polar ray. -/
noncomputable def idealHexagonSideProjection (i : Fin 6) (θ : ℝ) : ℝ :=
  (star (idealHexagonSideCenter i) *
    (Real.cos θ + Real.sin θ * Complex.I)).re

theorem idealHexagonSideEquation_polar (i : Fin 6) (p : ℝ × ℝ) :
    idealHexagonSideEquation i (Complex.polarCoord.symm p) =
      p.1 ^ 2 - 2 * p.1 * idealHexagonSideProjection i p.2 + 1 := by
  have hnorm : Complex.normSq (Complex.polarCoord.symm p) = p.1 ^ 2 := by
    rw [Complex.normSq_eq_norm_sq, Complex.norm_polarCoord_symm]
    exact sq_abs p.1
  rw [idealHexagonSideEquation, hnorm]
  rw [Complex.polarCoord_symm_apply]
  have hfactor :
      (star (idealHexagonSideCenter i) *
        ((p.1 : ℂ) * (Real.cos p.2 + Real.sin p.2 * Complex.I))).re =
      p.1 * idealHexagonSideProjection i p.2 := by
    rw [mul_left_comm]
    simp [idealHexagonSideProjection, Complex.mul_re]
  rw [hfactor]
  ring

/-- The smaller radial root of the ideal side-circle equation. -/
noncomputable def idealHexagonSideRadial (i : Fin 6) (θ : ℝ) : ℝ :=
  idealHexagonSideProjection i θ -
    Real.sqrt ((idealHexagonSideProjection i θ) ^ 2 - 1)

theorem idealHexagonSideRadial_on_circle (i : Fin 6) (θ : ℝ)
    (hprojection : 1 ≤ idealHexagonSideProjection i θ) :
    idealHexagonSideEquation i
      (Complex.polarCoord.symm (idealHexagonSideRadial i θ, θ)) = 0 := by
  rw [idealHexagonSideEquation_polar]
  simp only [idealHexagonSideRadial]
  have hsq : 0 ≤ (idealHexagonSideProjection i θ) ^ 2 - 1 := by
    nlinarith
  have hsqrt := Real.sq_sqrt hsq
  nlinarith

theorem idealHexagonSideEquation_polar_pos_iff_radial_lt
    (i : Fin 6) (θ r : ℝ)
    (hprojection : 1 ≤ idealHexagonSideProjection i θ)
    (hr : r < 1) :
    0 < idealHexagonSideEquation i (Complex.polarCoord.symm (r, θ)) ↔
      r < idealHexagonSideRadial i θ := by
  rw [idealHexagonSideEquation_polar]
  let u := idealHexagonSideProjection i θ
  have hu : 1 ≤ u := hprojection
  have hsq : 0 ≤ u ^ 2 - 1 := by nlinarith
  have hsqrt := Real.sq_sqrt hsq
  have hsqrt_nonneg := Real.sqrt_nonneg (u ^ 2 - 1)
  change 0 < r ^ 2 - 2 * r * u + 1 ↔
    r < u - Real.sqrt (u ^ 2 - 1)
  constructor
  · intro hpositive
    by_contra hnot
    have hsmall : u - Real.sqrt (u ^ 2 - 1) ≤ r := le_of_not_gt hnot
    have hlarge : r ≤ u + Real.sqrt (u ^ 2 - 1) := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hsmall) (sub_nonneg.mpr hlarge)]
  · intro hsmall
    have hleft : 0 < u - Real.sqrt (u ^ 2 - 1) - r := by linarith
    have hright : 0 < u + Real.sqrt (u ^ 2 - 1) - r := by linarith
    nlinarith [mul_pos hleft hright]

/-- Concrete disc-polar inequalities defining the six-sided ideal region. -/
noncomputable def idealHexagonDiscPolarBounds : Set (ℝ × ℝ) :=
  {p | p ∈ Complex.polarCoord.target ∧ p.1 < 1 ∧
    ∀ i : Fin 6,
      0 < p.1 ^ 2 - 2 * p.1 * idealHexagonSideProjection i p.2 + 1}

theorem idealHexagonDiscInterior_polar_iff (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ idealHexagonDiscInterior ↔
      p ∈ idealHexagonDiscPolarBounds := by
  have hrpos : 0 < p.1 := by
    simpa [Complex.polarCoord_target, Set.mem_prod] using hp.1
  simp only [idealHexagonDiscInterior, idealHexagonDiscPolarBounds,
    Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  simp only [hp, true_and, Metric.mem_ball, dist_zero_right,
    Complex.norm_polarCoord_symm, abs_of_pos hrpos,
    idealHexagonInwardHalfplane, Set.mem_ofPred_eq,
    idealHexagonSideEquation_polar]

theorem idealHexagonSideEquation_polar_pos_of_projection_lt_one
    (i : Fin 6) (θ r : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hprojection : idealHexagonSideProjection i θ < 1) :
    0 < idealHexagonSideEquation i (Complex.polarCoord.symm (r, θ)) := by
  rw [idealHexagonSideEquation_polar]
  have hsq : 0 < (1 - r) ^ 2 := sq_pos_of_pos (by linarith)
  have hmul : 0 ≤ r * (1 - idealHexagonSideProjection i θ) :=
    mul_nonneg hr0 (by linarith)
  nlinarith

/-- Every polar ray meets the ideal region exactly below the active side roots. -/
theorem idealHexagonDiscInterior_polar_iff_radial (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ idealHexagonDiscInterior ↔
      p.1 < 1 ∧
        ∀ i : Fin 6,
          1 ≤ idealHexagonSideProjection i p.2 →
            p.1 < idealHexagonSideRadial i p.2 := by
  have hrpos : 0 < p.1 := by
    simpa [Complex.polarCoord_target, Set.mem_prod] using hp.1
  rw [idealHexagonDiscInterior_polar_iff p hp]
  simp only [idealHexagonDiscPolarBounds, Set.mem_ofPred_eq, hp, true_and]
  constructor
  · rintro ⟨hr, hside⟩
    refine ⟨hr, ?_⟩
    intro i hi
    exact (idealHexagonSideEquation_polar_pos_iff_radial_lt
      i p.2 p.1 hi hr).1 (by
        rw [idealHexagonSideEquation_polar]
        exact hside i)
  · rintro ⟨hr, hroot⟩
    refine ⟨hr, ?_⟩
    intro i
    by_cases hi : 1 ≤ idealHexagonSideProjection i p.2
    · have h := (idealHexagonSideEquation_polar_pos_iff_radial_lt
        i p.2 p.1 hi hr).2 (hroot i hi)
      rwa [idealHexagonSideEquation_polar] at h
    · have h := idealHexagonSideEquation_polar_pos_of_projection_lt_one
        i p.2 p.1 hrpos.le hr (lt_of_not_ge hi)
      rwa [idealHexagonSideEquation_polar] at h

theorem idealHexagonDiscPolarBounds_isOpen :
    IsOpen idealHexagonDiscPolarBounds := by
  have hset : idealHexagonDiscPolarBounds =
      Complex.polarCoord.target ∩
        Complex.polarCoord.symm ⁻¹' idealHexagonDiscInterior := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, (idealHexagonDiscInterior_polar_iff p hp.1).2 hp⟩
    · rintro ⟨hp, hw⟩
      exact (idealHexagonDiscInterior_polar_iff p hp).1 hw
  rw [hset]
  exact Complex.polarCoord.continuousOn_symm.isOpen_inter_preimage
    Complex.polarCoord.open_target idealHexagonDiscInterior_isOpen

theorem idealHexagonDiscPolarBounds_measurable :
    MeasurableSet idealHexagonDiscPolarBounds :=
  idealHexagonDiscPolarBounds_isOpen.measurableSet

/-- Cayley's complex-coordinate formula, prior to restricting to the upper half-plane. -/
noncomputable def idealHexagonCayleyComplex (w : ℂ) : ℂ :=
  (w - Complex.I) / (w + Complex.I)

theorem idealHexagonInterior_coordinate_iff (w : ℂ) :
    w ∈ UpperHalfPlane.coe '' idealHexagonInterior ↔
      0 < w.im ∧
        ∀ i : Fin 6,
          0 < idealHexagonSideEquation i (idealHexagonCayleyComplex w) := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.im_pos, ?_⟩
    intro i
    have hdisc : (cayley z : ℂ) ∈ idealHexagonDiscInterior := hz
    have hside : (cayley z : ℂ) ∈ idealHexagonInwardHalfplane i :=
      (Set.mem_iInter.mp hdisc.2) i
    simpa [idealHexagonInwardHalfplane, idealHexagonCayleyComplex,
      cayley] using hside
  · rintro ⟨hw, hside⟩
    let z : UpperHalfPlane := ⟨w, hw⟩
    refine ⟨z, ?_, rfl⟩
    change (cayley z : ℂ) ∈ idealHexagonDiscInterior
    refine ⟨cayley_mem_ball z, Set.mem_iInter.mpr ?_⟩
    intro i
    change 0 < idealHexagonSideEquation i (cayley z : ℂ)
    simpa [idealHexagonCayleyComplex, cayley, z] using hside i

/-- The explicit upper-half-plane polar inequalities for the same ideal hexagon. -/
noncomputable def idealHexagonUpperPolarBounds : Set (ℝ × ℝ) :=
  {p | p ∈ Complex.polarCoord.target ∧
    0 < p.1 * Real.sin p.2 ∧
    ∀ i : Fin 6,
      0 < idealHexagonSideEquation i
        (idealHexagonCayleyComplex (Complex.polarCoord.symm p))}

theorem idealHexagonUpperPolarBounds_subset_target :
    idealHexagonUpperPolarBounds ⊆ Complex.polarCoord.target := by
  intro p hp
  exact hp.1

theorem idealHexagonInterior_upper_polar_iff (p : ℝ × ℝ)
    (hp : p ∈ Complex.polarCoord.target) :
    Complex.polarCoord.symm p ∈ UpperHalfPlane.coe '' idealHexagonInterior ↔
      p ∈ idealHexagonUpperPolarBounds := by
  have him : (Complex.polarCoord.symm p).im =
      p.1 * Real.sin p.2 := by
    simp [Complex.polarCoord_symm_apply, Complex.mul_im,
      Complex.sin_ofReal_re]
  rw [idealHexagonInterior_coordinate_iff]
  simp only [idealHexagonUpperPolarBounds, Set.mem_ofPred_eq, hp,
    true_and, him]

theorem idealHexagonUpperPolarBounds_isOpen :
    IsOpen idealHexagonUpperPolarBounds := by
  have hcoord : IsOpen (UpperHalfPlane.coe '' idealHexagonInterior) :=
    UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _
      idealHexagonInterior_isOpen
  have hset : idealHexagonUpperPolarBounds =
      Complex.polarCoord.target ∩
        Complex.polarCoord.symm ⁻¹'
          (UpperHalfPlane.coe '' idealHexagonInterior) := by
    ext p
    constructor
    · intro hp
      exact ⟨hp.1, (idealHexagonInterior_upper_polar_iff p hp.1).2 hp⟩
    · rintro ⟨hp, him⟩
      exact (idealHexagonInterior_upper_polar_iff p hp).1 him
  rw [hset]
  exact Complex.polarCoord.continuousOn_symm.isOpen_inter_preimage
    Complex.polarCoord.open_target hcoord

theorem idealHexagonUpperPolarBounds_measurable :
    MeasurableSet idealHexagonUpperPolarBounds :=
  idealHexagonUpperPolarBounds_isOpen.measurableSet

/-- The actual six-sided ideal region has the exact hyperbolic polar area
integral in upper-half-plane coordinates. -/
theorem idealHexagonInterior_volume_eq_polar_integral :
    (volume : Measure UpperHalfPlane) idealHexagonInterior =
      ∫⁻ p in idealHexagonUpperPolarBounds,
        ENNReal.ofReal p.1 *
          (↑((1 / ‖(Complex.polarCoord.symm p).im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by
  let S : Set ℂ := UpperHalfPlane.coe '' idealHexagonInterior
  let w : ℂ → ℝ≥0∞ := fun z => ↑((1 / ‖z.im‖₊) ^ 2 : NNReal)
  have hS : MeasurableSet S :=
    UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr
      idealHexagonInterior_measurable
  have hpolar :
      (∫⁻ z in S, w z) =
        ∫⁻ p in Complex.polarCoord.target,
          ENNReal.ofReal p.1 * (S.indicator w) (Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator hS]
    simpa only [Complex.polarCoord_target, polarCoord_target, smul_eq_mul] using
      (Complex.lintegral_comp_polarCoord_symm (S.indicator w)).symm
  have hregion :
      (∫⁻ p in Complex.polarCoord.target,
        ENNReal.ofReal p.1 * (S.indicator w) (Complex.polarCoord.symm p)) =
      ∫⁻ p in idealHexagonUpperPolarBounds,
        ENNReal.ofReal p.1 * w (Complex.polarCoord.symm p) := by
    rw [← lintegral_indicator Complex.polarCoord.open_target.measurableSet]
    rw [← lintegral_indicator idealHexagonUpperPolarBounds_measurable]
    congr 1
    funext p
    by_cases hp : p ∈ Complex.polarCoord.target
    · by_cases hpt : p ∈ idealHexagonUpperPolarBounds
      · have hps : Complex.polarCoord.symm p ∈ S :=
          (idealHexagonInterior_upper_polar_iff p hp).2 hpt
        simp only [Set.indicator_of_mem hp, Set.indicator_of_mem hpt,
          Set.indicator_of_mem hps]
      · have hps : Complex.polarCoord.symm p ∉ S := by
          exact fun h => hpt ((idealHexagonInterior_upper_polar_iff p hp).1 h)
        simp only [Set.indicator_of_mem hp, Set.indicator_of_notMem hpt,
          Set.indicator_of_notMem hps, mul_zero]
    · have hpt : p ∉ idealHexagonUpperPolarBounds :=
        fun h => hp (idealHexagonUpperPolarBounds_subset_target h)
      simp only [Set.indicator_of_notMem hp, Set.indicator_of_notMem hpt]
  calc
    (volume : Measure UpperHalfPlane) idealHexagonInterior =
        ∫⁻ z in S, w z := UpperHalfPlane.volume_eq_lintegral _
    _ = _ := hpolar.trans hregion

/-- The same area identity for the normalized Hausdorff measure. -/
theorem idealHexagonInterior_normalizedHausdorff_eq_polar_integral :
    (μHE[2] : Measure UpperHalfPlane) idealHexagonInterior =
      ∫⁻ p in idealHexagonUpperPolarBounds,
        ENNReal.ofReal p.1 *
          (↑((1 / ‖(Complex.polarCoord.symm p).im‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by
  rw [normalizedHausdorff_eq_upperHalfPlane_volume]
  exact idealHexagonInterior_volume_eq_polar_integral

/-- The ideal hexagon's actual upper-half-plane polar density is
`r / (r sin θ)^2` with Mathlib's nonnegative-real conventions. -/
theorem idealHexagonInterior_volume_eq_polar_integral_trig :
    (volume : Measure UpperHalfPlane) idealHexagonInterior =
      ∫⁻ p in idealHexagonUpperPolarBounds,
        ENNReal.ofReal p.1 *
          (↑((1 / ‖p.1 * Real.sin p.2‖₊) ^ 2 : NNReal) : ℝ≥0∞) := by
  have him (p : ℝ × ℝ) : (Complex.polarCoord.symm p).im =
      p.1 * Real.sin p.2 := by
    simp [Complex.polarCoord_symm_apply, Complex.mul_im,
      Complex.sin_ofReal_re]
  simpa only [him] using idealHexagonInterior_volume_eq_polar_integral

end CurveComplex.Hyperbolic
