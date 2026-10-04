import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.ChartTransitionDerivative
import CurveComplexGenusTwo.Topology.ActualLocalAnalyticSheaves.LocalSheafScaffold
import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.ActualOneFormBridge
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

open scoped Manifold ContDiff Bundle Topology
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace SameAtlasAnalyticCohomology
universe u v
variable {E : Type u} [TopologicalSpace E] [ChartedSpace ℂ E]
  [IsManifold 𝓘(ℂ) ∞ E]

theorem chartTransitionDerivative_ne_zero (a b x : E)
    (ha : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℂ) b).source) :
    chartTransitionDerivative a b x ≠ 0 := by
  intro hq
  have hq' : tangentCoordChange 𝓘(ℂ) a b x 1 = 0 := by
    simpa [tangentCoordChange_def, chartTransitionDerivative, mfld_simps] using hq
  have hc := tangentCoordChange_comp (I := 𝓘(ℂ))
    (w := a) (x := b) (y := a) (z := x) (v := (1 : ℂ)) ⟨⟨ha, hb⟩, ha⟩
  rw [hq', map_zero, tangentCoordChange_self ha] at hc
  exact zero_ne_one hc

/-- The chart's coordinate vector, constructed from the derivative of its
inverse and transported along the chart inverse equality to the fiber at `x`.
The model-space tangent identification is canonical; no arbitrary tangent
identification on the surface is used. -/
noncomputable def inverseChartTangentFrame (a x : E)
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) : TangentSpace 𝓘(ℂ) x :=
  let c := extChartAt 𝓘(ℂ) a
  let v := (mfderiv[Set.range 𝓘(ℂ)] c.symm (c x))
    ((NormedSpace.fromTangentSpace (c x)).symm 1)
  Eq.mp (congrArg (TangentSpace 𝓘(ℂ)) (c.left_inv hx)) v

/-- The coefficient of `s = h(z) dz` in chart `a`, defined by evaluating
`s` on the actual derivative-defined coordinate vector. -/
noncomputable def chartCanonicalCoefficient (a x : E)
    (s : ActualCanonicalSection E) : ℂ := by
  classical
  exact if hx : x ∈ (extChartAt 𝓘(ℂ) a).source
    then s x (inverseChartTangentFrame a x hx) else 0

/-- Explicit coefficient formula on the source of its chart. -/
theorem chartCanonicalCoefficient_inverseChartDerivative (a x : E)
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (s : ActualCanonicalSection E) :
    chartCanonicalCoefficient a x s =
      s x (inverseChartTangentFrame a x hx) := by
  simp only [chartCanonicalCoefficient, dite_eq_left hx]

/-- The constructed vector agrees with Mathlib's geometric tangent-bundle
trivialization, whose derivative identity is in `MFDeriv.Atlas`. -/
theorem inverseChartTangentFrame_eq_trivialization (a x : E)
    (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) :
    inverseChartTangentFrame a x hx =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) a).symmL ℂ x 1 := by
  rw [TangentBundle.symmL_trivializationAt (I := 𝓘(ℂ)) (by simpa using hx)]
  unfold inverseChartTangentFrame
  simp only [NormedSpace.fromTangentSpace, tangentSpaceCastModel]
  rfl

theorem chartCanonicalCoefficient_transition (a b x : E)
    (ha : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℂ) b).source)
    (s : ActualCanonicalSection E) :
    chartCanonicalCoefficient b x s =
      chartCanonicalCoefficient a x s / chartTransitionDerivative a b x := by
  have ha' : x ∈ (chartAt ℂ a).source := by simpa using ha
  have hb' : x ∈ (chartAt ℂ b).source := by simpa using hb
  have hbridge (c : E) (hc : x ∈ (extChartAt 𝓘(ℂ) c).source) :
      chartCanonicalCoefficient c x s =
        CanonicalDimensionTwo.actualLocalOneForm s c ((chartAt ℂ c) x)
          (fun _ : Fin 1 => (1 : ℂ)) := by
    rw [chartCanonicalCoefficient_inverseChartDerivative c x hc s,
      inverseChartTangentFrame_eq_trivialization c x hc]
    exact (CanonicalDimensionTwo.actualLocalOneForm_eq_global_in_chart
      s c x 1 (by simpa using hc)).symm
  have hframe : chartTransitionDerivative a b x •
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) b).symmL ℂ x 1 =
      (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) a).symmL ℂ x 1 := by
    rw [TangentBundle.symmL_trivializationAt_eq_core hb',
      TangentBundle.symmL_trivializationAt_eq_core ha']
    change chartTransitionDerivative a b x • tangentCoordChange 𝓘(ℂ) b x x 1 =
      tangentCoordChange 𝓘(ℂ) a x x 1
    have hc := tangentCoordChange_comp (I := 𝓘(ℂ))
      (w := a) (x := b) (y := x) (z := x) (v := (1 : ℂ))
      ⟨⟨ha, hb⟩, mem_extChartAt_source x⟩
    simpa [tangentCoordChange_def, chartTransitionDerivative, mfld_simps,
      ← smul_eq_mul, map_smul] using hc
  have hcoeff : chartCanonicalCoefficient a x s =
      chartTransitionDerivative a b x * chartCanonicalCoefficient b x s := by
    rw [hbridge a ha, hbridge b hb,
      CanonicalDimensionTwo.actualLocalOneForm_eq_global_in_chart s a x 1 ha',
      CanonicalDimensionTwo.actualLocalOneForm_eq_global_in_chart s b x 1 hb']
    change s x _ = chartTransitionDerivative a b x * s x _
    rw [← hframe, map_smul]
    rfl
  apply (eq_div_iff (chartTransitionDerivative_ne_zero a b x ha hb)).mpr
  simpa [mul_comm] using hcoeff.symm

/-- Real Wirtinger differentiation of a complex-valued function in chart `a`.
The coefficient multiplies `d(bar z)` in the source's convention. -/
noncomputable def chartDbar (a : E) (f : E → ℂ) (x : E) : ℂ :=
  let c := extChartAt 𝓘(ℂ) a
  let d := fderiv ℝ (fun z : ℂ => f (c.symm z)) (c x)
  (d 1 + Complex.I * d Complex.I) / 2

noncomputable def chartDbarWeight (a : E) (ρ : E → ℝ) (x : E) : ℂ :=
  chartDbar a (fun y => (ρ y : ℂ)) x

theorem chartDbar_transition (a b x : E) (f : E → ℂ)
    (ha : x ∈ (extChartAt 𝓘(ℂ) a).source)
    (hb : x ∈ (extChartAt 𝓘(ℂ) b).source)
    (hf : ContDiffAt ℝ 1 (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z))
      ((extChartAt 𝓘(ℂ) a) x)) :
    chartDbar b f x = chartDbar a f x /
      star (chartTransitionDerivative a b x) := by
  let A := fderiv ℝ (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z))
    ((extChartAt 𝓘(ℂ) a) x)
  let R := tangentCoordChange 𝓘(ℂ) b a x
  let r : ℂ := R 1
  have hT : HasFDerivAt
      ((extChartAt 𝓘(ℂ) a) ∘ (extChartAt 𝓘(ℂ) b).symm) R
      ((extChartAt 𝓘(ℂ) b) x) := by
    have ht := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ)) ⟨hb, ha⟩
    simp only [mfld_simps] at ht
    exact ht.hasFDerivAt (by simp)
  have hval : ((extChartAt 𝓘(ℂ) a) ∘ (extChartAt 𝓘(ℂ) b).symm)
      ((extChartAt 𝓘(ℂ) b) x) = (extChartAt 𝓘(ℂ) a) x := by
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ) b).left_inv hb]
  have hF : HasFDerivAt
      (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z)) A
      ((extChartAt 𝓘(ℂ) a) x) :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have hF' : HasFDerivAt
      (fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z)) A
      (((extChartAt 𝓘(ℂ) a) ∘ (extChartAt 𝓘(ℂ) b).symm)
        ((extChartAt 𝓘(ℂ) b) x)) := by
    rw [hval]
    exact hF
  have hcomp := hF'.comp ((extChartAt 𝓘(ℂ) b) x) (hT.restrictScalars ℝ)
  have hnear : ∀ᶠ z in 𝓝 ((extChartAt 𝓘(ℂ) b) x),
      (extChartAt 𝓘(ℂ) b).symm z ∈ (extChartAt 𝓘(ℂ) a).source := by
    have ht := continuousAt_extChartAt_symm' hb
    have hs : (extChartAt 𝓘(ℂ) a).source ∈
        𝓝 ((extChartAt 𝓘(ℂ) b).symm ((extChartAt 𝓘(ℂ) b) x)) := by
      simpa only [(extChartAt 𝓘(ℂ) b).left_inv hb] using
        extChartAt_source_mem_nhds' ha
    exact ht.preimage_mem_nhds hs
  have heq : (fun z : ℂ => f ((extChartAt 𝓘(ℂ) b).symm z)) =ᶠ[
      𝓝 ((extChartAt 𝓘(ℂ) b) x)]
      ((fun z : ℂ => f ((extChartAt 𝓘(ℂ) a).symm z)) ∘
        ((extChartAt 𝓘(ℂ) a) ∘ (extChartAt 𝓘(ℂ) b).symm)) := by
    filter_upwards [hnear] with z hz
    simp only [Function.comp_apply, (extChartAt 𝓘(ℂ) a).left_inv hz]
  have hB : fderiv ℝ (fun z : ℂ => f ((extChartAt 𝓘(ℂ) b).symm z))
      ((extChartAt 𝓘(ℂ) b) x) = A.comp (R.restrictScalars ℝ) :=
    heq.fderiv_eq.trans hcomp.fderiv
  have hrq : r * chartTransitionDerivative a b x = 1 := by
    have hc := tangentCoordChange_comp (I := 𝓘(ℂ))
      (w := a) (x := b) (y := a) (z := x) (v := (1 : ℂ)) ⟨⟨ha, hb⟩, ha⟩
    rw [tangentCoordChange_self ha] at hc
    have hq : tangentCoordChange 𝓘(ℂ) a b x 1 = chartTransitionDerivative a b x := by
      simp only [tangentCoordChange_def, chartTransitionDerivative, mfld_simps, fderivWithin_univ]
    rw [hq] at hc
    have hr : tangentCoordChange 𝓘(ℂ) b a x (chartTransitionDerivative a b x) =
        chartTransitionDerivative a b x * r := by
      simp [r, R, smul_eq_mul]
    rw [hr] at hc
    simpa [mul_comm] using hc
  have hR (v : ℂ) : R v = r * v := by
    simpa [r, smul_eq_mul, mul_comm] using R.map_smul v (1 : ℂ)
  have hanti : A r + Complex.I * A (r * Complex.I) =
      star r * (A 1 + Complex.I * A Complex.I) := by
    have hA (z : ℂ) : A z = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
      calc
        A z = A (z.re • (1 : ℂ) + z.im • Complex.I) := by
          congr 1
          simp only [RCLike.real_smul_eq_coe_mul, mul_one]
          exact (Complex.re_add_im z).symm
        _ = (z.re : ℂ) * A 1 + (z.im : ℂ) * A Complex.I := by
          rw [map_add, map_smul, map_smul]
          simp only [RCLike.real_smul_eq_coe_mul]
          rfl
    rw [hA r, hA (r * Complex.I)]
    have hstar : star r = (r.re : ℂ) - (r.im : ℂ) * Complex.I := by
      apply Complex.ext <;> simp
    rw [hstar]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      mul_zero, mul_one, zero_sub, Complex.ofReal_neg]
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp only [chartDbar, hB, ContinuousLinearMap.comp_apply]
  change (A (R 1) + Complex.I * A (R Complex.I)) / 2 =
    ((A 1 + Complex.I * A Complex.I) / 2) / star (chartTransitionDerivative a b x)
  rw [hR 1, hR Complex.I, mul_one]
  rw [hanti]
  apply (eq_div_iff (star_ne_zero.mpr
    (chartTransitionDerivative_ne_zero a b x ha hb))).mpr
  have hs : star r * star (chartTransitionDerivative a b x) = 1 := by
    simpa only [star_mul, star_one, mul_comm] using congrArg star hrq
  calc
    (star r * (A 1 + Complex.I * A Complex.I) / 2) *
        star (chartTransitionDerivative a b x) =
      (star r * star (chartTransitionDerivative a b x)) *
        ((A 1 + Complex.I * A Complex.I) / 2) := by ring
    _ = (A 1 + Complex.I * A Complex.I) / 2 := by rw [hs, one_mul]


end SameAtlasAnalyticCohomology
