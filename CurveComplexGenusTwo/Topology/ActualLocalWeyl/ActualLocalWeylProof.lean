import CurveComplexGenusTwo.Topology.ActualLocalWeyl.HarmonicRecovery
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualLocalDbarContracts
import CurveComplexGenusTwo.Topology.ActualLocalWeyl.ActualLocalCurrentUniqueness
import CurveComplexGenusTwo.Topology.ActualLocalDbarSolvability.ActualDbarHolomorphicKernel
import Mathlib.Analysis.Distribution.Distribution
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

open scoped ContDiff Distributions
open TopologicalSpace MeasureTheory

namespace CanonicalDimensionTwo.LocalDbar.WeylProof

private theorem test_derivative_commute (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤)
    (u v : ℂ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ u
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) =
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ u φ) := by
  ext z
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply,
    le_top, ↓reduceIte]
  change fderiv ℝ (fun x => fderiv ℝ φ x v) z u =
    fderiv ℝ (fun x => fderiv ℝ φ x u) z v
  have hf : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((φ.contDiff.fderiv_right (m := ∞) (by simp)).differentiable (by simp)).differentiableAt
  rw [fderiv_clm_apply hf (differentiableAt_const v),
    fderiv_clm_apply hf (differentiableAt_const u)]
  simpa using φ.contDiff.contDiffAt.isSymmSndFDerivAt (x := z) (by simp) u v

#print axioms test_derivative_commute

private theorem test_dbar_eq (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤) :
    testDbar Ω φ = (2 : ℂ)⁻¹ •
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ 1 φ +
       Complex.I • TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ Complex.I φ) := by
  ext z
  simp [testDbar]

private theorem weak_cr (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ φ, T (testDbar Ω φ) = 0) (φ : TestFunction Ω ℂ ⊤) :
    T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ 1 φ) +
      Complex.I * T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ Complex.I φ) = 0 := by
  have h := hT φ
  rw [test_dbar_eq, map_smul, map_add, map_smul] at h
  simpa using h

private theorem weak_coordinate_laplacian (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ φ, T (testDbar Ω φ) = 0) (φ : TestFunction Ω ℂ ⊤) :
    T (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ 1
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ 1 φ) +
       TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ Complex.I
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ Complex.I φ)) = 0 := by
  have h₁ := weak_cr Ω T hT (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ 1 φ)
  have h₂ := weak_cr Ω T hT
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ Complex.I φ)
  rw [test_derivative_commute Ω φ Complex.I 1] at h₁
  rw [map_add]
  have hi (a b c : ℂ) : a + c = (a + Complex.I * b) -
      Complex.I * (b + Complex.I * c) := by
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I]
    ring
  rw [hi, h₁, h₂]
  simp

#print axioms weak_coordinate_laplacian

private noncomputable def realTestDistribution (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ) : Distribution Ω ℂ ⊤ where
  toFun φ := T (TestFunction.postcompCLM Complex.ofRealCLM φ)
  map_add' φ ψ := by simp
  map_smul' r φ := by simp [T.map_smul_of_tower]
  cont := T.continuous.comp (TestFunction.postcompCLM Complex.ofRealCLM).continuous

private theorem complexify_derivative (Ω : Opens ℂ)
    (φ : TestFunction Ω ℝ ⊤) (v : ℂ) :
    TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) =
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v
      (TestFunction.postcompCLM Complex.ofRealCLM φ) := by
  ext z
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply,
    le_top, ↓reduceIte, TestFunction.postcompCLM_apply, Function.comp_apply]
  change Complex.ofRealCLM (fderiv ℝ φ z v) =
    fderiv ℝ (Complex.ofRealCLM ∘ φ) z v
  rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
    (φ.contDiff.differentiable (by simp)).differentiableAt,
    Complex.ofRealCLM.fderiv]
  rfl

private theorem realTestDistribution_laplacian_zero (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ φ, T (testDbar Ω φ) = 0) :
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) (1 : ℂ)
        (realTestDistribution Ω T)) +
    Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
      (Distribution.lineDerivCLM (n := ⊤) (k := ⊤) Complex.I
        (realTestDistribution Ω T)) = 0 := by
  ext φ
  simp only [add_apply, Distribution.lineDerivCLM_apply, neg_neg, zero_apply]
  change T (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ 1
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ 1 φ))) +
    T (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I
        (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ Complex.I φ))) = 0
  simp only [complexify_derivative]
  rw [← map_add]
  exact weak_coordinate_laplacian Ω T hT
    (TestFunction.postcompCLM Complex.ofRealCLM φ)

#print axioms realTestDistribution_laplacian_zero

private theorem complex_test_reconstruction (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤) :
    TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.reCLM φ) +
    Complex.I • TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.imCLM φ) = φ := by
  ext z
  simpa [mul_comm] using (Complex.re_add_im (φ z))

private theorem realTestDistribution_injective (Ω : Opens ℂ) :
    Function.Injective (realTestDistribution Ω) := by
  intro T S h
  ext φ
  have hr := congrArg (fun D : Distribution Ω ℂ ⊤ =>
    D (TestFunction.postcompCLM Complex.reCLM φ)) h
  have hi := congrArg (fun D : Distribution Ω ℂ ⊤ =>
    D (TestFunction.postcompCLM Complex.imCLM φ)) h
  change T (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.reCLM φ)) =
    S (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.reCLM φ)) at hr
  change T (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.imCLM φ)) =
    S (TestFunction.postcompCLM Complex.ofRealCLM
      (TestFunction.postcompCLM Complex.imCLM φ)) at hi
  calc
    T φ = T (TestFunction.postcompCLM Complex.ofRealCLM
        (TestFunction.postcompCLM Complex.reCLM φ) +
      Complex.I • TestFunction.postcompCLM Complex.ofRealCLM
        (TestFunction.postcompCLM Complex.imCLM φ)) := by rw [complex_test_reconstruction]
    _ = S (TestFunction.postcompCLM Complex.ofRealCLM
        (TestFunction.postcompCLM Complex.reCLM φ) +
      Complex.I • TestFunction.postcompCLM Complex.ofRealCLM
        (TestFunction.postcompCLM Complex.imCLM φ)) := by simp only [map_add, map_smul, hr, hi]
    _ = S φ := by rw [complex_test_reconstruction]

#print axioms realTestDistribution_injective

private theorem smooth_directional_continuousOn (Ω : Opens ℂ) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ ∞ h Ω) (v : ℂ) :
    ContinuousOn (fun z => fderiv ℝ h z v) Ω :=
  (hh.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply continuousOn_const

private theorem smooth_dbar_continuousOn (Ω : Opens ℂ) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ ∞ h Ω) : ContinuousOn (dbar h) Ω := by
  unfold dbar
  exact ((smooth_directional_continuousOn Ω hh 1).add
    (continuousOn_const.mul (smooth_directional_continuousOn Ω hh Complex.I))).div_const 2

private theorem test_fderiv_formula (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤)
    (v z : ℂ) :
    TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ z = fderiv ℝ φ z v := by
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply,
    le_top, ↓reduceIte]

private theorem local_integrable_test_product (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤)
    {h : ℂ → ℂ} (hh : ContinuousOn h Ω) :
    Integrable (fun z => φ z * h z) := by
  simpa using φ.integrable_bilin (ContinuousLinearMap.mul ℂ ℂ)
    (hh.locallyIntegrableOn Ω.isOpen.measurableSet)

private theorem integration_by_parts_on_open (Ω : Opens ℂ)
    (φ : TestFunction Ω ℂ ⊤) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ ∞ h Ω) (v : ℂ) :
    (∫ z : ℂ, φ z * fderiv ℝ h z v) =
      -(∫ z : ℂ, fderiv ℝ φ z v * h z) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · simpa only [test_fderiv_formula] using local_integrable_test_product Ω
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) hh.continuousOn
  · exact local_integrable_test_product Ω φ (smooth_directional_continuousOn Ω hh v)
  · exact local_integrable_test_product Ω φ hh.continuousOn
  · intro z _
    exact (φ.contDiff.differentiable (by simp)).differentiableAt
  · intro z hz
    exact (hh.differentiableOn (by simp)).differentiableAt
      (Ω.isOpen.mem_nhds (φ.tsupport_subset hz))

private theorem integration_by_parts_dbar (Ω : Opens ℂ)
    (φ : TestFunction Ω ℂ ⊤) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ ∞ h Ω) :
    (∫ z : ℂ, φ z * dbar h z) = -(∫ z : ℂ, dbar φ z * h z) := by
  have hhI (v : ℂ) : Integrable (fun z => φ z * fderiv ℝ h z v) :=
    local_integrable_test_product Ω φ (smooth_directional_continuousOn Ω hh v)
  have hφI (v : ℂ) : Integrable (fun z => fderiv ℝ φ z v * h z) := by
    simpa only [test_fderiv_formula] using local_integrable_test_product Ω
      (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℂ v φ) hh.continuousOn
  have he₁ (z : ℂ) : φ z * dbar h z =
      (φ z * fderiv ℝ h z 1 + Complex.I * (φ z * fderiv ℝ h z Complex.I)) / 2 := by
    dsimp [dbar]
    ring
  have he₂ (z : ℂ) : dbar φ z * h z =
      (fderiv ℝ φ z 1 * h z + Complex.I * (fderiv ℝ φ z Complex.I * h z)) / 2 := by
    dsimp [dbar]
    ring
  simp only [he₁, he₂, integral_div, integral_add (hhI 1) ((hhI Complex.I).const_mul _),
    integral_add (hφI 1) ((hφI Complex.I).const_mul _), integral_const_mul,
    integration_by_parts_on_open Ω φ hh]
  ring

#print axioms integration_by_parts_dbar

private theorem smooth_representative_analytic (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ φ, T (testDbar Ω φ) = 0) {h : ℂ → ℂ}
    (hh : ContDiffOn ℝ ∞ h Ω)
    (hrep : ∀ φ : TestFunction Ω ℂ ⊤,
      T φ = ∫ z : ℂ, (2 * Complex.I) * φ z * h z) : AnalyticOnNhd ℂ h Ω := by
  have hweak (φ : TestFunction Ω ℂ ⊤) : (∫ z : ℂ, φ z * dbar h z) = 0 := by
    rw [integration_by_parts_dbar Ω φ hh, neg_eq_zero]
    have hz := (hrep (testDbar Ω φ)).symm.trans (hT φ)
    simp only [testDbar_apply, mul_assoc, integral_const_mul] at hz
    simpa only [mul_eq_zero, OfNat.ofNat_ne_zero, Complex.I_ne_zero, false_or] using hz
  have hc : localCoefficientCurrent Ω (dbar h) = localCoefficientCurrent Ω 0 := by
    ext φ
    rw [localCoefficientCurrent_apply Ω (dbar h)
      ((smooth_dbar_continuousOn Ω hh).locallyIntegrableOn Ω.isOpen.measurableSet),
      localCoefficientCurrent_apply Ω 0
      (continuousOn_const.locallyIntegrableOn Ω.isOpen.measurableSet)]
    simp only [mul_assoc, integral_const_mul, hweak, Pi.zero_apply, mul_zero, integral_zero]
  have hzero := localCoefficientCurrent_injective_on_continuous Ω
    (smooth_dbar_continuousOn Ω hh) continuousOn_const hc
  apply (CanonicalDimensionTwo.actualSmooth_dbar_zero_iff_analyticOnNhd Ω.isOpen hh).mp
  intro z hz
  exact hzero hz

#print axioms smooth_representative_analytic

private theorem realTestDistribution_current (Ω : Opens ℂ) {h : ℂ → ℂ}
    (hh : ContinuousOn h Ω) :
    realTestDistribution Ω (localCoefficientCurrent Ω h) =
      Distribution.ofFun Ω (fun z => (2 * Complex.I) * h z) volume ⊤ := by
  have hmul : ContinuousOn (fun z => (2 * Complex.I) * h z) Ω :=
    continuousOn_const.mul hh
  ext φ
  change localCoefficientCurrent Ω h (TestFunction.postcompCLM Complex.ofRealCLM φ) = _
  rw [localCoefficientCurrent_apply Ω h
    (hh.locallyIntegrableOn Ω.isOpen.measurableSet),
    Distribution.ofFun_apply (hmul.locallyIntegrableOn Ω.isOpen.measurableSet)]
  congr 1
  ext z
  simp only [TestFunction.postcompCLM_apply, Function.comp_apply,
    Complex.ofRealCLM_apply, Complex.real_smul]
  ring

private theorem real_distribution_smooth_representation (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ ∞ g Ω)
    (hrep : realTestDistribution Ω T = Distribution.ofFun Ω g volume ⊤) :
    ∃ h : ℂ → ℂ, ContDiffOn ℝ ∞ h Ω ∧
      ∀ φ : TestFunction Ω ℂ ⊤,
        T φ = ∫ z : ℂ, (2 * Complex.I) * φ z * h z := by
  let h : ℂ → ℂ := fun z => g z / (2 * Complex.I)
  have hh : ContDiffOn ℝ ∞ h Ω := hg.div_const _
  refine ⟨h, hh, ?_⟩
  have he : T = localCoefficientCurrent Ω h := by
    apply realTestDistribution_injective Ω
    rw [hrep, realTestDistribution_current Ω hh.continuousOn]
    congr 1
    funext z
    dsimp [h]
    field_simp
  intro φ
  rw [he, localCoefficientCurrent_apply Ω h
    (hh.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)]

#print axioms real_distribution_smooth_representation

private theorem analytic_representative_of_smooth_real_representation (Ω : Opens ℂ)
    (T : TestFunction Ω ℂ ⊤ →L[ℂ] ℂ)
    (hT : ∀ φ, T (testDbar Ω φ) = 0) {g : ℂ → ℂ}
    (hg : ContDiffOn ℝ ∞ g Ω)
    (hrep : realTestDistribution Ω T = Distribution.ofFun Ω g volume ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h Ω ∧
      ∀ φ : TestFunction Ω ℂ ⊤,
        T φ = ∫ z : ℂ, (2 * Complex.I) * φ z * h z := by
  obtain ⟨h, hh, hrep⟩ := real_distribution_smooth_representation Ω T hg hrep
  exact ⟨h, smooth_representative_analytic Ω T hT hh hrep, hrep⟩

#print axioms analytic_representative_of_smooth_real_representation

end CanonicalDimensionTwo.LocalDbar.WeylProof

namespace CanonicalDimensionTwo.LocalDbar

/-- An actual continuous complex-linear current annihilating the literal dbar
operator has the analytic coefficient with the original 2I normalization. -/
theorem actualLocalWeylCurrent : ActualLocalWeylCurrentStatement := by
  intro c R hR T hT
  let Ω : Opens ℂ := ⟨Metric.ball c R, Metric.isOpen_ball⟩
  obtain ⟨g, hg, hrep⟩ := actualDiskHarmonicDistributionSmoothRepresentative c R hR
    (WeylProof.realTestDistribution Ω T)
    (WeylProof.realTestDistribution_laplacian_zero Ω T hT)
  exact WeylProof.analytic_representative_of_smooth_real_representation Ω T hT hg hrep

#print axioms actualLocalWeylCurrent

end CanonicalDimensionTwo.LocalDbar
