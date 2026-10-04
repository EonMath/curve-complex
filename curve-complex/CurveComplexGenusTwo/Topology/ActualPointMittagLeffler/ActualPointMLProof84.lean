import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualPointDetectionCanonicalInterface
import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartTestExtensionDbarV2
import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartTestFormContinuityV2
import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualPointMLDependencies84
import CurveComplexGenusTwo.Topology.ActualPointMittagLeffler.ActualChartCutoffContourV2
import CurveComplexGenusTwo.Topology.ActualTwoOpenCechBridge.ActualTwoOpenCechBridge
import CurveComplexGenusTwo.Topology.ActualAnalyticCohomology.DolbeaultDbar
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Topology.ContinuousMap.LocallyConvex
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.MeasureTheory.Function.Jacobian

open TopologicalSpace SameAtlasRRLocal SameAtlasAnalyticCohomology MeasureTheory
open CanonicalDimensionTwo.LocalDbar
open scoped Manifold ContDiff Bundle Distributions Topology
set_option maxHeartbeats 2500000
set_option synthInstance.maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

namespace CanonicalDimensionTwo

/-- The exact original one-point Mittag-Leffler detection statement. All
current localization, gluing, and partition calculations are local proof
steps; the original atlas and literal obstruction/evaluation maps persist. -/
theorem actualPointMittagLefflerDetection
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) (A : ChartedSpace ℂ E)
    (hA : letI : ChartedSpace ℂ E := A; IsManifold 𝓘(ℂ) ∞ E) :
    ActualPointMittagLefflerDetectionStatement E hg A hA := by
  classical
  letI : CurveComplex.ClosedSurface E := Classical.choice hg.2.1
  letI : ChartedSpace ℂ E := A
  letI : IsManifold 𝓘(ℂ) ∞ E := hA
  let L : SmoothZeroOne E →ₗ[ℂ] (∀ (a : E) (n : ℕ), C(ChartTarget a, RealJet n)) :=
    { toFun := fun f a n => smoothZeroOneJet a n f
      map_add' := by
        intro f g
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          ((fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w)) +
           (fun w : ℂ => g.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_add_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
          ((g.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp))
      map_smul' := by
        intro c f
        funext a n
        apply ContinuousMap.ext
        intro z
        change iteratedFDeriv ℝ n
          (c • (fun w : ℂ => f.1 a ((extChartAt 𝓘(ℂ) a).symm w))) z.1 = _
        exact iteratedFDeriv_const_smul_apply
          ((f.property.2.1 a).contDiffAt ((isOpen_extChartAt_target a).mem_nhds z.property)
            |>.of_le (by simp)) }
  letI : LocallyConvexSpace ℝ (SmoothZeroOne E) :=
    LocallyConvexSpace.induced (L.restrictScalars ℝ)
  have hseparate (S : Submodule ℂ (SmoothZeroOne E)) (hS : IsClosed (S : Set (SmoothZeroOne E)))
      (α : SmoothZeroOne E) (hα : α ∉ S) :
      ∃ T : SmoothZeroOne E →L[ℂ] ℂ, (∀ β ∈ S, T β = 0) ∧ T α ≠ 0 := by
    obtain ⟨T, u, hTu, hu⟩ := RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (S.restrictScalars ℝ).convex hS hα
    have hu0 : 0 < u := by simpa using hTu 0 S.zero_mem
    have hzero (β : SmoothZeroOne E) (hβ : β ∈ S) : T β = 0 := by
      by_contra hb
      have hlt := hTu ((((u + 1 : ℝ) : ℂ) / (T β)) • β) (S.smul_mem _ hβ)
      rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hb] at hlt
      change u + 1 < u at hlt
      linarith
    refine ⟨T, hzero, ?_⟩
    intro h
    rw [h] at hu
    change u < 0 at hu
    linarith
  have hextDbar (a : E) (φ : TestFunction (actualChartTestOpen a) ℂ ⊤) :
      dolbeaultDbar (actualChartTestScalarExtension a φ) =
        actualChartTestFormExtension a (testDbar _ φ) := by
    apply Subtype.ext
    funext b x
    by_cases hx : x ∈ (extChartAt 𝓘(ℂ) b).source
    · change (if x ∈ (extChartAt 𝓘(ℂ) b).source then
        chartDbar b (actualChartTestScalarExtension a φ).1 x else 0) = _
      rw [ite_eq_left hx]
      exact actualChartTestExtension_dbar a b x hx φ
    · exact (show (dolbeaultDbar (actualChartTestScalarExtension a φ)).1 b x = 0 from
        (dolbeaultDbar (actualChartTestScalarExtension a φ)).property.1 b x hx).trans
        ((actualChartTestFormExtension a (testDbar _ φ)).property.1 b x hx).symm
  let chartExtension (a : E) : TestFunction (actualChartTestOpen a) ℂ ⊤ →L[ℂ]
      SmoothZeroOne E :=
    ⟨actualChartTestFormExtension a, actualChartTestFormExtension_continuous a⟩
  have hchartClosed (T : SmoothZeroOne E →L[ℂ] ℂ)
      (hT : ∀ f : SmoothZero E, T (dolbeaultDbar f) = 0) (a : E)
      (φ : TestFunction (actualChartTestOpen a) ℂ ⊤) :
      (T.comp (chartExtension a)) (testDbar _ φ) = 0 := by
    change T (actualChartTestFormExtension a (testDbar _ φ)) = 0
    rw [← hextDbar]
    exact hT _
  have hmonoDbar (Ω Ω' : Opens ℂ) (hΩ : Ω ≤ Ω')
      (φ : TestFunction Ω ℂ ⊤) :
      (TestFunction.monoCLM ℂ : TestFunction Ω ℂ ⊤ →L[ℂ] TestFunction Ω' ℂ ⊤)
          (testDbar Ω φ) =
        testDbar Ω' (TestFunction.monoCLM ℂ φ) := by
    apply TestFunction.ext
    have hφ : ((TestFunction.monoCLM ℂ φ : TestFunction Ω' ℂ ⊤) : ℂ → ℂ) = φ := by
      simp only [TestFunction.monoCLM_apply, le_refl, hΩ, and_self, ite_true]
    intro z
    rw [show (TestFunction.monoCLM ℂ (testDbar Ω φ) : TestFunction Ω' ℂ ⊤) z =
      (testDbar Ω φ) z by simp only [TestFunction.monoCLM_apply, le_refl, hΩ, and_self, ite_true]]
    rw [testDbar_apply, testDbar_apply, hφ]
  have hdiskRepresentative (T : SmoothZeroOne E →L[ℂ] ℂ)
      (hT : ∀ f : SmoothZero E, T (dolbeaultDbar f) = 0) (a : E)
      (c : ℂ) (R : ℝ) (hR : 0 < R)
      (hball : Metric.ball c R ⊆ (extChartAt 𝓘(ℂ) a).target) :
      ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball c R) ∧
        ∀ φ : TestFunction (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
          T (actualChartTestFormExtension a (TestFunction.monoCLM ℂ φ)) =
            ∫ z : ℂ, (2 * Complex.I) * φ z * h z := by
    let Ω : Opens ℂ := ⟨Metric.ball c R, Metric.isOpen_ball⟩
    let J : TestFunction Ω ℂ ⊤ →L[ℂ] TestFunction (actualChartTestOpen a) ℂ ⊤ :=
      TestFunction.monoCLM ℂ
    let Ta := (T.comp (chartExtension a)).comp J
    apply actualLocalWeylCurrent c R hR Ta
    intro φ
    change (T.comp (chartExtension a)) (J (testDbar Ω φ)) = 0
    rw [show J (testDbar Ω φ) = testDbar _ (J φ) from hmonoDbar Ω _ hball φ]
    exact hchartClosed T hT a (J φ)
  have hmonoComp (Ω₀ Ω₁ Ω₂ : Opens ℂ) (h01 : Ω₀ ≤ Ω₁) (h12 : Ω₁ ≤ Ω₂)
      (φ : TestFunction Ω₀ ℂ ⊤) :
      (TestFunction.monoCLM ℂ : TestFunction Ω₁ ℂ ⊤ →L[ℂ] TestFunction Ω₂ ℂ ⊤)
        (TestFunction.monoCLM ℂ φ) = TestFunction.monoCLM ℂ φ := by
    ext z
    simp only [TestFunction.monoCLM_apply, le_refl, h01, h12, h01.trans h12,
      and_self, ite_true]
  have hrestrictUnique (Ω₀ Ω₁ Ω₂ Ω : Opens ℂ)
      (h10 : Ω₁ ≤ Ω₀) (h20 : Ω₂ ≤ Ω₀) (h1 : Ω ≤ Ω₁) (h2 : Ω ≤ Ω₂)
      (T : TestFunction Ω₀ ℂ ⊤ →L[ℂ] ℂ) (h k : ℂ → ℂ)
      (hh : AnalyticOnNhd ℂ h Ω₁) (hk : AnalyticOnNhd ℂ k Ω₂)
      (hrep : ∀ φ : TestFunction Ω₁ ℂ ⊤,
        T (TestFunction.monoCLM ℂ φ) = ∫ z : ℂ, (2 * Complex.I) * φ z * h z)
      (krep : ∀ φ : TestFunction Ω₂ ℂ ⊤,
        T (TestFunction.monoCLM ℂ φ) = ∫ z : ℂ, (2 * Complex.I) * φ z * k z) :
      Set.EqOn h k Ω := by
    apply localCoefficientCurrent_injective_on_continuous Ω
      (hh.mono h1).continuousOn (hk.mono h2).continuousOn
    ext φ
    rw [localCoefficientCurrent_apply Ω h
      ((hh.mono h1).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet),
      localCoefficientCurrent_apply Ω k
      ((hk.mono h2).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)]
    have hhφ := hrep (TestFunction.monoCLM ℂ φ)
    have hkφ := krep (TestFunction.monoCLM ℂ φ)
    rw [hmonoComp Ω Ω₁ Ω₀ h1 h10] at hhφ
    rw [hmonoComp Ω Ω₂ Ω₀ h2 h20] at hkφ
    have hi1 : ((TestFunction.monoCLM ℂ φ : TestFunction Ω₁ ℂ ⊤) : ℂ → ℂ) = φ := by
      simp only [TestFunction.monoCLM_apply, le_refl, h1, and_self, ite_true]
    have hi2 : ((TestFunction.monoCLM ℂ φ : TestFunction Ω₂ ℂ ⊤) : ℂ → ℂ) = φ := by
      simp only [TestFunction.monoCLM_apply, le_refl, h2, and_self, ite_true]
    rw [hi1] at hhφ
    rw [hi2] at hkφ
    exact hhφ.symm.trans hkφ
  have hchartAnalyticDensity (T : SmoothZeroOne E →L[ℂ] ℂ)
      (hT : ∀ f : SmoothZero E, T (dolbeaultDbar f) = 0) (a : E) :
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (extChartAt 𝓘(ℂ) a).target ∧
        ∀ (c : ℂ) (R : ℝ) (hR : 0 < R)
          (hball : Metric.ball c R ⊆ (extChartAt 𝓘(ℂ) a).target)
          (k : ℂ → ℂ) (hk : AnalyticOnNhd ℂ k (Metric.ball c R)),
          (∀ φ : TestFunction (⟨Metric.ball c R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
            T (actualChartTestFormExtension a (TestFunction.monoCLM ℂ φ)) =
              ∫ z : ℂ, (2 * Complex.I) * φ z * k z) →
          Set.EqOn H k (Metric.ball c R) := by
    let Ω₀ := actualChartTestOpen a
    let Ta := T.comp (chartExtension a)
    have hlocal (z : ChartTarget a) : ∃ R : ℝ, 0 < R ∧
        Metric.ball z.1 R ⊆ (extChartAt 𝓘(ℂ) a).target ∧
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball z.1 R) ∧
          ∀ φ : TestFunction (⟨Metric.ball z.1 R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
            Ta (TestFunction.monoCLM ℂ φ) = ∫ w : ℂ, (2 * Complex.I) * φ w * h w := by
      obtain ⟨R, hR, hB⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target a) z.1 z.property
      obtain ⟨h, hh, hrep⟩ := hdiskRepresentative T hT a z.1 R hR hB
      exact ⟨R, hR, hB, h, hh, hrep⟩
    choose R hR hB h hh hrep using hlocal
    let Ω (z : ChartTarget a) : Opens ℂ := ⟨Metric.ball z.1 (R z), Metric.isOpen_ball⟩
    let H : ℂ → ℂ := fun z => if hz : z ∈ (extChartAt 𝓘(ℂ) a).target then h ⟨z, hz⟩ z else 0
    have hcompat (z w : ChartTarget a) : Set.EqOn (h z) (h w) (Ω z ⊓ Ω w) :=
      hrestrictUnique Ω₀ (Ω z) (Ω w) (Ω z ⊓ Ω w) (hB z) (hB w)
        inf_le_left inf_le_right Ta (h z) (h w) (hh z) (hh w) (hrep z) (hrep w)
    have hEq (z : ChartTarget a) : Set.EqOn H (h z) (Ω z) := by
      intro w hw
      have hwt : w ∈ (extChartAt 𝓘(ℂ) a).target := hB z hw
      change (if hz : w ∈ (extChartAt 𝓘(ℂ) a).target then h ⟨w, hz⟩ w else 0) = h z w
      rw [dite_eq_left hwt]
      exact hcompat ⟨w, hwt⟩ z ⟨Metric.mem_ball_self (hR _), hw⟩
    refine ⟨H, ?_, ?_⟩
    · intro z hz
      apply (hh ⟨z, hz⟩ z (Metric.mem_ball_self (hR _))).congr
      filter_upwards [Metric.ball_mem_nhds z (hR ⟨z, hz⟩)] with w hw
      exact (hEq ⟨z, hz⟩ hw).symm
    · intro c r hr hball k hk krep z hz
      have hzt := hball hz
      let Ω' : Opens ℂ := ⟨Metric.ball c r, Metric.isOpen_ball⟩
      have he := hrestrictUnique Ω₀ (Ω ⟨z, hzt⟩) Ω' (Ω ⟨z, hzt⟩ ⊓ Ω')
        (hB ⟨z, hzt⟩) hball inf_le_left inf_le_right Ta (h ⟨z, hzt⟩) k
        (hh ⟨z, hzt⟩) hk (hrep ⟨z, hzt⟩) krep
      change (if hz : z ∈ (extChartAt 𝓘(ℂ) a).target then h ⟨z, hz⟩ z else 0) = k z
      rw [dite_eq_left hzt]
      exact he ⟨Metric.mem_ball_self (hR _), hz⟩
  have hwholeChartRepresentative (T : SmoothZeroOne E →L[ℂ] ℂ)
      (hT : ∀ f : SmoothZero E, T (dolbeaultDbar f) = 0) (a : E) :
      ∃ H : ℂ → ℂ, AnalyticOnNhd ℂ H (extChartAt 𝓘(ℂ) a).target ∧
        ∀ φ : TestFunction (actualChartTestOpen a) ℂ ⊤,
          T (actualChartTestFormExtension a φ) =
            ∫ z : ℂ, (2 * Complex.I) * φ z * H z := by
    obtain ⟨H, hH, hHeq⟩ := hchartAnalyticDensity T hT a
    refine ⟨H, hH, ?_⟩
    intro φ
    let Ω₀ := actualChartTestOpen a
    let Ta := T.comp (chartExtension a)
    have hlocal (z : ChartTarget a) : ∃ R : ℝ, 0 < R ∧
        Metric.ball z.1 R ⊆ (extChartAt 𝓘(ℂ) a).target ∧
        ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h (Metric.ball z.1 R) ∧
          ∀ ψ : TestFunction (⟨Metric.ball z.1 R, Metric.isOpen_ball⟩ : Opens ℂ) ℂ ⊤,
            Ta (TestFunction.monoCLM ℂ ψ) = ∫ w : ℂ, (2 * Complex.I) * ψ w * h w := by
      obtain ⟨R, hR, hB⟩ := Metric.isOpen_iff.mp (isOpen_extChartAt_target a) z.1 z.property
      obtain ⟨h, hh, hrep⟩ := hdiskRepresentative T hT a z.1 R hR hB
      exact ⟨R, hR, hB, h, hh, hrep⟩
    choose R hR hB h hh hrep using hlocal
    let Ω (z : ChartTarget a) : Opens ℂ := ⟨Metric.ball z.1 (R z), Metric.isOpen_ball⟩
    have hcover : tsupport (φ : ℂ → ℂ) ⊆ ⋃ z : ChartTarget a, (Ω z : Set ℂ) := by
      intro z hz
      have hzt := φ.tsupport_subset hz
      exact Set.mem_iUnion.mpr ⟨⟨z, hzt⟩, Metric.mem_ball_self (hR _)⟩
    obtain ⟨J, hJ⟩ := φ.hasCompactSupport.elim_finite_subcover
      (fun z : ChartTarget a => (Ω z : Set ℂ)) (fun z => (Ω z).isOpen) hcover
    have hcoverJ : tsupport (φ : ℂ → ℂ) ⊆ ⋃ z : J, (Ω z.1 : Set ℂ) := by
      intro z hz
      obtain ⟨w, hw, hzw⟩ := Set.mem_iUnion₂.mp (hJ hz)
      exact Set.mem_iUnion.mpr ⟨⟨w, hw⟩, hzw⟩
    obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, ℂ)
      φ.hasCompactSupport.isClosed (fun z : J => (Ω z.1 : Set ℂ))
      (fun z => (Ω z.1).isOpen) hcoverJ
    let ψ (j : J) : TestFunction (Ω j.1) ℂ ⊤ :=
      ⟨fun z => ρ j z • φ z,
        (contMDiff_iff_contDiff.mp (ρ j).contMDiff).smul φ.contDiff,
        φ.hasCompactSupport.smul_left (f := fun z : ℂ => ρ j z),
        (tsupport_smul_subset_left _ _).trans (hρ j)⟩
    let ψ₀ (j : J) : TestFunction Ω₀ ℂ ⊤ := TestFunction.monoCLM ℂ (ψ j)
    have hψ₀ (j : J) : (ψ₀ j : ℂ → ℂ) = fun z => ρ j z • φ z := by
      change ((TestFunction.monoCLM ℂ (ψ j) : TestFunction Ω₀ ℂ ⊤) : ℂ → ℂ) = _
      simp only [TestFunction.monoCLM_apply, le_refl, (show Ω j.1 ≤ Ω₀ from hB j.1), and_self, ite_true]
      rfl
    have hsum : φ = ∑ j : J, ψ₀ j := by
      apply TestFunction.ext
      intro z
      change φ z = (⇑(∑ j : J, ψ₀ j)) z
      simp only [FunLike.coe_sum, Finset.sum_apply, hψ₀]
      by_cases hz : φ z = 0
      · simp only [hz, smul_zero, Finset.sum_const_zero]
      · have hs := ρ.sum_eq_one (subset_tsupport (φ : ℂ → ℂ) hz)
        rw [finsum_eq_sum_of_fintype] at hs
        rw [← Finset.sum_smul, hs, one_smul]
    let TH := localCoefficientCurrent Ω₀ H
    have hTH (χ : TestFunction Ω₀ ℂ ⊤) :
        TH χ = ∫ z : ℂ, (2 * Complex.I) * χ z * H z :=
      localCoefficientCurrent_apply Ω₀ H
        (hH.continuousOn.locallyIntegrableOn (isOpen_extChartAt_target a).measurableSet) χ
    have hterms (j : J) : Ta (ψ₀ j) = TH (ψ₀ j) := by
      rw [hTH]
      change Ta (TestFunction.monoCLM ℂ (ψ j)) = _
      rw [hrep j.1 (ψ j), hψ₀]
      apply integral_congr_ae
      filter_upwards [] with z
      by_cases hz : z ∈ Ω j.1
      · have he := hHeq j.1.1 (R j.1) (hR j.1) (hB j.1) (h j.1) (hh j.1) (hrep j.1) hz
        change (2 * Complex.I) * (ρ j z • φ z) * h j.1 z = _
        rw [he]
      · have hp : ψ j z = 0 := (ψ j).zero_on_compl hz
        have hp' : ρ j z • φ z = 0 := hp
        simp only [hp, hp', mul_zero, zero_mul]
    calc
      T (actualChartTestFormExtension a φ) = Ta φ := rfl
      _ = Ta (∑ j : J, ψ₀ j) := congrArg Ta hsum
      _ = TH (∑ j : J, ψ₀ j) := by simp only [map_sum, hterms]
      _ = TH φ := congrArg TH hsum.symm
      _ = ∫ z : ℂ, (2 * Complex.I) * φ z * H z := hTH φ
  have htransfer (a b : E) (φ : TestFunction (actualChartTestOpen a) ℂ ⊤)
      (hsupp : ∀ z ∈ tsupport (φ : ℂ → ℂ),
        (extChartAt 𝓘(ℂ) a).symm z ∈ (extChartAt 𝓘(ℂ) b).source) :
      ∃ ψ : TestFunction (actualChartTestOpen b) ℂ ⊤,
        tsupport (ψ : ℂ → ℂ) ⊆ (extChartAt 𝓘(ℂ) b) ''
          ((extChartAt 𝓘(ℂ) a).symm '' tsupport (φ : ℂ → ℂ)) ∧
        actualChartTestFormExtension b ψ = actualChartTestFormExtension a φ ∧
        ∀ z ∈ (extChartAt 𝓘(ℂ) a).target,
          (extChartAt 𝓘(ℂ) a).symm z ∈ (extChartAt 𝓘(ℂ) b).source →
          ψ ((extChartAt 𝓘(ℂ) b) ((extChartAt 𝓘(ℂ) a).symm z)) =
            φ z / star (chartTransitionDerivative a b ((extChartAt 𝓘(ℂ) a).symm z)) := by
    let ca := extChartAt 𝓘(ℂ) a
    let cb := extChartAt 𝓘(ℂ) b
    let α := actualChartTestFormExtension a φ
    let K : Set ℂ := cb '' (ca.symm '' tsupport (φ : ℂ → ℂ))
    have hKa : IsCompact (ca.symm '' tsupport (φ : ℂ → ℂ)) :=
      φ.hasCompactSupport.image_of_continuousOn
        ((continuousOn_extChartAt_symm a).mono φ.tsupport_subset)
    have hsubb : ca.symm '' tsupport (φ : ℂ → ℂ) ⊆ cb.source := by
      rintro x ⟨z, hz, rfl⟩
      exact hsupp z hz
    have hK : IsCompact K := hKa.image_of_continuousOn
      ((continuousOn_extChartAt b).mono hsubb)
    have hKt : K ⊆ cb.target := by
      rintro z ⟨x, hx, rfl⟩
      exact cb.map_source (hsubb hx)
    let ψfun : ℂ → ℂ := fun z => if z ∈ cb.target then α.1 b (cb.symm z) else 0
    have hsK : Function.support ψfun ⊆ K := by
      intro z hz
      change ψfun z ≠ 0 at hz
      have hzt : z ∈ cb.target := by
        by_contra hn
        exact hz (ite_eq_right hn)
      have hα : α.1 b (cb.symm z) ≠ 0 := by
        simpa only [ψfun, ite_eq_left hzt] using hz
      have hxa : cb.symm z ∈ ca.source := by
        by_contra hn
        apply hα
        change (if cb.symm z ∈ ca.source ∧ cb.symm z ∈ cb.source then _ else 0) = 0
        rw [ite_eq_right (fun h => hn h.1)]
      have hφ : φ (ca (cb.symm z)) ≠ 0 := by
        intro hf
        apply hα
        change (if cb.symm z ∈ ca.source ∧ cb.symm z ∈ cb.source then _ else 0) = 0
        rw [ite_eq_left ⟨hxa, cb.map_target hzt⟩, hf, zero_div]
      exact ⟨cb.symm z, ⟨ca (cb.symm z), subset_tsupport (φ : ℂ → ℂ) hφ,
        ca.left_inv hxa⟩, cb.right_inv hzt⟩
    have htK : tsupport ψfun ⊆ K := closure_minimal hsK hK.isClosed
    have hψdiff : ContDiff ℝ ∞ ψfun := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ cb.target
      · have hc := (α.property.2.1 b).contDiffAt ((isOpen_extChartAt_target b).mem_nhds hz)
        apply hc.congr_of_eventuallyEq
        filter_upwards [(isOpen_extChartAt_target b).mem_nhds hz] with w hw
        exact ite_eq_left hw
      · have hzK : z ∉ K := fun h => hz (hKt h)
        have he : ψfun =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
          filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hzK] with w hw
          exact image_eq_zero_of_notMem_tsupport (fun h => hw (htK h))
        exact contDiffAt_const.congr_of_eventuallyEq he
    let ψ : TestFunction (actualChartTestOpen b) ℂ ⊤ :=
      ⟨ψfun, hψdiff, hK.of_isClosed_subset (isClosed_tsupport ψfun) htK, htK.trans hKt⟩
    have hvalue (x : E) (hx : x ∈ cb.source) : ψ (cb x) = α.1 b x := by
      change (if cb x ∈ cb.target then α.1 b (cb.symm (cb x)) else 0) = _
      rw [ite_eq_left (cb.map_source hx), cb.left_inv hx]
    have hzero (d x : E) (hx : x ∉ cb.source) : α.1 d x = 0 := by
      change (if x ∈ ca.source ∧ x ∈ (extChartAt 𝓘(ℂ) d).source then _ else 0) = 0
      split_ifs with hx'
      · have hp : φ (ca x) = 0 := by
          by_contra hn
          have hm := hsupp (ca x) (subset_tsupport (φ : ℂ → ℂ) hn)
          rw [ca.left_inv hx'.1] at hm
          exact hx hm
        rw [hp, zero_div]
      · rfl
    refine ⟨ψ, htK, ?_, ?_⟩
    · apply Subtype.ext
      funext d x
      by_cases hx : x ∈ cb.source
      · by_cases hd : x ∈ (extChartAt 𝓘(ℂ) d).source
        · change (if x ∈ cb.source ∧ x ∈ (extChartAt 𝓘(ℂ) d).source then _ else 0) = _
          rw [ite_eq_left ⟨hx, hd⟩, hvalue x hx]
          exact (α.property.2.2 b d x hx hd).symm
        · exact ((actualChartTestFormExtension b ψ).property.1 d x hd).trans
            (α.property.1 d x hd).symm
      · change (if x ∈ cb.source ∧ x ∈ (extChartAt 𝓘(ℂ) d).source then _ else 0) = _
        rw [ite_eq_right (fun h => hx h.1), hzero d x hx]
    · intro z hz hb
      rw [hvalue (ca.symm z) hb]
      change (if ca.symm z ∈ ca.source ∧ ca.symm z ∈ cb.source then _ else 0) = _
      rw [ite_eq_left ⟨ca.map_target hz, hb⟩, ca.right_inv hz]
  have hJac (a b : E) (z : ℂ)
      (hz : z ∈ (extChartAt 𝓘(ℂ) a).target)
      (hb : (extChartAt 𝓘(ℂ) a).symm z ∈ (extChartAt 𝓘(ℂ) b).source) :
      ∃ L : ℂ →L[ℝ] ℂ,
        HasFDerivAt ((extChartAt 𝓘(ℂ) b) ∘ (extChartAt 𝓘(ℂ) a).symm) L z ∧
        L.det = ‖chartTransitionDerivative a b ((extChartAt 𝓘(ℂ) a).symm z)‖ ^ 2 := by
    let x := (extChartAt 𝓘(ℂ) a).symm z
    have hxa : x ∈ (extChartAt 𝓘(ℂ) a).source := (extChartAt 𝓘(ℂ) a).map_target hz
    have h := hasFDerivWithinAt_tangentCoordChange (I := 𝓘(ℂ)) (x := a) (y := b)
      (z := x) ⟨hxa, hb⟩
    have h' : HasFDerivAt ((extChartAt 𝓘(ℂ) b) ∘ (extChartAt 𝓘(ℂ) a).symm)
        (tangentCoordChange 𝓘(ℂ) a b x) z := by
      simpa only [x, modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ,
        (extChartAt 𝓘(ℂ) a).right_inv hz] using h
    refine ⟨(tangentCoordChange 𝓘(ℂ) a b x).restrictScalars ℝ, h'.restrictScalars ℝ, ?_⟩
    have heq : tangentCoordChange 𝓘(ℂ) a b x =
        ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℂ ℂ)
          (chartTransitionDerivative a b x) := by
      apply ContinuousLinearMap.ext
      intro w
      have hq : tangentCoordChange 𝓘(ℂ) a b x 1 = chartTransitionDerivative a b x := by
        simp [chartTransitionDerivative, mfld_simps]
      have hm := (tangentCoordChange 𝓘(ℂ) a b x).map_smul w (1 : ℂ)
      simpa only [smul_eq_mul, mul_one, hq, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply] using hm
    rw [heq]
    simp [ContinuousLinearMap.det, LinearMap.det_restrictScalars,
      Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq, x]
  have htransition (T : SmoothZeroOne E →L[ℂ] ℂ) (a b : E) (h k : ℂ → ℂ)
      (hh : AnalyticOnNhd ℂ h (extChartAt 𝓘(ℂ) a).target)
      (hk : AnalyticOnNhd ℂ k (extChartAt 𝓘(ℂ) b).target)
      (hrep : ∀ φ : TestFunction (actualChartTestOpen a) ℂ ⊤,
        T (actualChartTestFormExtension a φ) = ∫ z : ℂ, (2 * Complex.I) * φ z * h z)
      (krep : ∀ φ : TestFunction (actualChartTestOpen b) ℂ ⊤,
        T (actualChartTestFormExtension b φ) = ∫ z : ℂ, (2 * Complex.I) * φ z * k z)
      (x : E) (hxa : x ∈ (extChartAt 𝓘(ℂ) a).source)
      (hxb : x ∈ (extChartAt 𝓘(ℂ) b).source) :
      k ((extChartAt 𝓘(ℂ) b) x) =
        h ((extChartAt 𝓘(ℂ) a) x) / chartTransitionDerivative a b x := by
    let ca := extChartAt 𝓘(ℂ) a
    let cb := extChartAt 𝓘(ℂ) b
    let U := ca.symm ≫ cb
    have hUopen : IsOpen U.source := by
      apply isOpen_iff_mem_nhds.mpr
      intro z hz
      exact Filter.inter_mem ((isOpen_extChartAt_target a).mem_nhds hz.1)
        ((continuousAt_extChartAt_symm'' (I := 𝓘(ℂ)) hz.1).preimage_mem_nhds
          ((isOpen_extChartAt_source b).mem_nhds hz.2))
    let Ω : Opens ℂ := ⟨U.source, hUopen⟩
    let q : ℂ → ℂ := fun z => chartTransitionDerivative a b (ca.symm z)
    let F : ℂ → ℂ := fun z => q z * k (U z)
    have hUtarget (z : ℂ) (hz : z ∈ U.source) : U z ∈ cb.target :=
      cb.map_source hz.2
    have hcontF : ContinuousOn F Ω := by
      intro z hz
      have hcd : ContDiffAt ℂ ∞ (cb ∘ ca.symm) z := by
        have hc := contDiffWithinAt_ext_coord_change (I := 𝓘(ℂ)) (n := ∞) b a hz
        simpa [ca, cb, contDiffWithinAt_univ] using hc
      have hq : ContinuousAt q z := by
        have he : q =ᶠ[𝓝 z] (fun w => (fderiv ℂ (cb ∘ ca.symm) w) 1) := by
          filter_upwards [(isOpen_extChartAt_target a).mem_nhds hz.1] with w hw
          change chartTransitionDerivative a b (ca.symm w) = _
          have hw' : (chartAt ℂ a) ((chartAt ℂ a).symm w) = w := by
            simpa [ca] using ca.right_inv hw
          simp [chartTransitionDerivative, ca, cb, hw']
        have ht : ContinuousAt (fun w => (fderiv ℂ (cb ∘ ca.symm) w) 1) z :=
          ((hcd.fderiv_right (m := ∞) (by simp)).clm_apply contDiffAt_const).continuousAt
        exact ht.congr_of_eventuallyEq he
      have hk' : ContinuousAt (fun w => k (U w)) z :=
        (hk (U z) (hUtarget z hz)).continuousAt.comp hcd.continuousAt
      exact (hq.mul hk').continuousWithinAt
    have hEq : Set.EqOn h F Ω := by
      apply localCoefficientCurrent_injective_on_continuous Ω (hh.continuousOn.mono (fun z hz => hz.1)) hcontF
      ext φ
      rw [localCoefficientCurrent_apply Ω h
        ((hh.continuousOn.mono (fun z hz => hz.1)).locallyIntegrableOn Ω.isOpen.measurableSet),
        localCoefficientCurrent_apply Ω F (hcontF.locallyIntegrableOn Ω.isOpen.measurableSet)]
      let φa : TestFunction (actualChartTestOpen a) ℂ ⊤ := TestFunction.monoCLM ℂ φ
      have hφa : (φa : ℂ → ℂ) = φ := by
        simp only [φa, TestFunction.monoCLM_apply, le_refl,
          (show Ω ≤ actualChartTestOpen a from fun z hz => hz.1), and_self, ite_true]
      have hφsupp : ∀ z ∈ tsupport (φa : ℂ → ℂ), ca.symm z ∈ cb.source := by
        intro z hz
        rw [hφa] at hz
        exact (φ.tsupport_subset hz).2
      obtain ⟨ψ, hψsupp, hψext, hψvalue⟩ := htransfer a b φa hφsupp
      have heq : (∫ z : ℂ, (2 * Complex.I) * φ z * h z) =
          ∫ z : ℂ, (2 * Complex.I) * ψ z * k z := by
        rw [← hφa, ← hrep φa, ← krep ψ, hψext]
      rw [heq]
      have hψtarget : tsupport (ψ : ℂ → ℂ) ⊆ U.target := by
        intro z hz
        obtain ⟨y, ⟨w, hw, hy⟩, hz⟩ := hψsupp hz
        subst y z
        rw [hφa] at hw
        exact U.map_source (φ.tsupport_subset hw)
      have hleft : (∫ z : ℂ, (2 * Complex.I) * ψ z * k z) =
          ∫ z in U.target, (2 * Complex.I) * ψ z * k z := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        have hp : ψ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hψtarget h))
        simp only [hp, mul_zero, zero_mul]
      have hright : (∫ z : ℂ, (2 * Complex.I) * φ z * F z) =
          ∫ z in U.source, (2 * Complex.I) * φ z * F z := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro z hz
        simp only [φ.zero_on_compl hz, Pi.zero_apply, mul_zero, zero_mul]
      rw [hleft, hright]
      have hDer (z : ℂ) (hz : z ∈ U.source) :
          HasFDerivAt U (fderiv ℝ U z) z ∧
            (fderiv ℝ U z).det = ‖q z‖ ^ 2 := by
        obtain ⟨L, hL, hdet⟩ := hJac a b z hz.1 hz.2
        change HasFDerivAt U L z at hL
        exact ⟨hL.differentiableAt.hasFDerivAt, by rw [hL.fderiv]; exact hdet⟩
      rw [← U.image_source_eq_target,
        integral_image_eq_integral_abs_det_fderiv_smul volume hUopen.measurableSet
          (fun z hz => (hDer z hz).1.hasFDerivWithinAt) U.injOn]
      apply setIntegral_congr_fun hUopen.measurableSet
      intro z hz
      dsimp only
      rw [(hDer z hz).2, abs_of_nonneg (sq_nonneg _)]
      have hv := hψvalue z hz.1 hz.2
      change ψ (U z) = φa z / star (q z) at hv
      rw [hv, hφa]
      change ‖q z‖ ^ 2 • ((2 * Complex.I) * (φ z / star (q z)) * k (U z)) =
        (2 * Complex.I) * φ z * (q z * k (U z))
      rw [Complex.real_smul, Complex.ofReal_pow, ← Complex.mul_conj']
      have hq : q z ≠ 0 := chartTransitionDerivative_ne_zero a b (ca.symm z)
        (ca.map_target hz.1) hz.2
      have hqstar : star (q z) ≠ 0 := star_ne_zero.mpr hq
      simp only [starRingEnd_apply] at hqstar ⊢
      field_simp
    have hxU : ca x ∈ Ω := by
      change ca x ∈ ca.target ∧ ca.symm (ca x) ∈ cb.source
      exact ⟨ca.map_source hxa, by rw [ca.left_inv hxa]; exact hxb⟩
    have hx := hEq hxU
    change h (ca x) = q (ca x) * k (U (ca x)) at hx
    change h (ca x) = chartTransitionDerivative a b (ca.symm (ca x)) *
      k (cb (ca.symm (ca x))) at hx
    rw [ca.left_inv hxa] at hx
    apply (eq_div_iff (chartTransitionDerivative_ne_zero a b x hxa hxb)).2
    simpa only [mul_comm] using hx.symm
  have hsection (h : E → ℂ → ℂ)
      (hh : ∀ a, AnalyticOnNhd ℂ (h a) (extChartAt 𝓘(ℂ) a).target)
      (htrans : ∀ a b x, x ∈ (extChartAt 𝓘(ℂ) a).source →
        x ∈ (extChartAt 𝓘(ℂ) b).source →
        h b ((extChartAt 𝓘(ℂ) b) x) =
          h a ((extChartAt 𝓘(ℂ) a) x) / chartTransitionDerivative a b x) :
      ∃ s : ActualCanonicalSection E, ∀ a x,
        x ∈ (extChartAt 𝓘(ℂ) a).source →
          chartCanonicalCoefficient a x s = h a ((extChartAt 𝓘(ℂ) a) x) := by
    let sfun (x : E) : TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial E ℂ x :=
      h x ((extChartAt 𝓘(ℂ) x) x) •
        (trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) x).continuousLinearMapAt ℂ x
    have hframe (a x : E) (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) (v : ℂ) :
        sfun x ((trivializationAt ℂ (TangentSpace 𝓘(ℂ) : E → Type _) a).symmL ℂ x v) =
          h a ((extChartAt 𝓘(ℂ) a) x) * v := by
      have hx' : x ∈ (chartAt ℂ a).source := by simpa using hx
      dsimp only [sfun]
      rw [smul_apply,
        TangentBundle.continuousLinearMapAt_trivializationAt_eq_core (mem_chart_source ℂ x),
        TangentBundle.symmL_trivializationAt_eq_core hx']
      change h x ((extChartAt 𝓘(ℂ) x) x) •
        tangentCoordChange 𝓘(ℂ) x x x (tangentCoordChange 𝓘(ℂ) a x x v) = _
      rw [tangentCoordChange_self (mem_extChartAt_source x)]
      have hv : tangentCoordChange 𝓘(ℂ) a x x v = v * chartTransitionDerivative a x x := by
        have hl := (tangentCoordChange 𝓘(ℂ) a x x).map_smul v (1 : ℂ)
        have hq : tangentCoordChange 𝓘(ℂ) a x x 1 = chartTransitionDerivative a x x := by
          simp only [tangentCoordChange_def, chartTransitionDerivative, mfld_simps, fderivWithin_univ]
        simpa only [smul_eq_mul, mul_one, hq] using hl
      rw [hv, htrans a x x hx (mem_extChartAt_source x), smul_eq_mul]
      field_simp [chartTransitionDerivative_ne_zero a x x hx (mem_extChartAt_source x)]
    let s : ActualCanonicalSection E := ⟨sfun, by
      intro a
      apply (contMDiffAt_hom_bundle _).2
      refine ⟨contMDiffAt_id, ?_⟩
      have hc : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ) ∞
          (fun x : E => h a ((extChartAt 𝓘(ℂ) a) x)) a := by
        exact (hh a _ (mem_extChartAt_target a)).contDiffAt.contMDiffAt.comp a
          (contMDiffAt_extChartAt (x := a))
      have ht : ContMDiffAt 𝓘(ℂ) 𝓘(ℂ, ℂ →L[ℂ] ℂ) ∞
          (fun x : E => h a ((extChartAt 𝓘(ℂ) a) x) • ContinuousLinearMap.id ℂ ℂ) a :=
        hc.smul contMDiffAt_const
      apply ht.congr_of_eventuallyEq
      filter_upwards [extChartAt_source_mem_nhds (I := 𝓘(ℂ)) a] with x hx
      apply ContinuousLinearMap.ext
      intro v
      simp only [ContinuousLinearMap.inCoordinates, Bundle.Trivial.fiberBundle_trivializationAt',
        ContinuousLinearMap.comp_apply, smul_apply, ContinuousLinearMap.id_apply]
      simpa using hframe a x hx v⟩
    refine ⟨s, ?_⟩
    intro a x hx
    rw [chartCanonicalCoefficient_inverseChartDerivative a x hx s,
      inverseChartTangentFrame_eq_trivialization a x hx]
    change sfun x _ = _
    rw [hframe a x hx 1, mul_one]
  have hglobalSection_localRepresentation (T : SmoothZeroOne E →L[ℂ] ℂ)
      (hT : ∀ f : SmoothZero E, T (dolbeaultDbar f) = 0) :
      ∃ s : ActualCanonicalSection E, ∀ (a : E) (φ : TestFunction (actualChartTestOpen a) ℂ ⊤),
        T (actualChartTestFormExtension a φ) =
          ∫ z : ℂ, (2 * Complex.I) * φ z *
            chartCanonicalCoefficient a ((extChartAt 𝓘(ℂ) a).symm z) s := by
    choose h hh hrep using hwholeChartRepresentative T hT
    have ht (a b x : E) (ha : x ∈ (extChartAt 𝓘(ℂ) a).source)
        (hb : x ∈ (extChartAt 𝓘(ℂ) b).source) :
        h b ((extChartAt 𝓘(ℂ) b) x) =
          h a ((extChartAt 𝓘(ℂ) a) x) / chartTransitionDerivative a b x :=
      htransition T a b (h a) (h b) (hh a) (hh b) (hrep a) (hrep b) x ha hb
    obtain ⟨s, hs⟩ := hsection h hh ht
    refine ⟨s, ?_⟩
    intro a φ
    rw [hrep a φ]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ (extChartAt 𝓘(ℂ) a).target
    · rw [hs a _ ((extChartAt 𝓘(ℂ) a).map_target hz), (extChartAt 𝓘(ℂ) a).right_inv hz]
    · have hφ : φ z = 0 := φ.zero_on_compl hz
      simp only [hφ, mul_zero, zero_mul]
  letI (p : E) (U : Opens E) (hp : p ∈ U) :
      Fintype (actualPunctureCechCover p U hp).Index := inferInstanceAs (Fintype Bool)
  have hpartition_one_near (p : E) (U : Opens E) (hp : p ∈ U)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p U hp)) :
      ∀ᶠ x in 𝓝 p, P.weight false x = 1 := by
    have hn : p ∉ tsupport (P.weight true) := by
      intro hx
      have hpunct := P.supportWeight true hx
      simpa [actualPunctureCechCover, puncturedOpen] using hpunct
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hn] with x hx
    have hone := P.partitionOne x
    change (∑ i : Bool, P.weight i x) = 1 at hone
    simpa [Fintype.sum_bool, hx] using hone
  have hpartition_dbar_sum (p : E) (U : Opens E) (hp : p ∈ U)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p U hp))
      (a x : E) (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) :
      chartDbarWeight a (P.weight false) x +
        chartDbarWeight a (P.weight true) x = 0 := by
    let c := extChartAt 𝓘(ℂ) a
    have hd (i : Bool) : DifferentiableAt ℝ
        (fun z : ℂ => (P.weight i (c.symm z) : ℂ)) (c x) := by
      exact Complex.ofRealCLM.differentiableAt.comp (c x)
        (((P.smoothWeight i a).contDiffAt
          (extChartAt_target_mem_nhds' (c.map_source hx))).differentiableAt (by simp))
    have he : (fun z : ℂ => (P.weight false (c.symm z) : ℂ) +
        (P.weight true (c.symm z) : ℂ)) = fun _ => (1 : ℂ) := by
      funext z
      have hsum := P.partitionOne (c.symm z)
      change (∑ i : Bool, P.weight i (c.symm z)) = 1 at hsum
      simpa [Fintype.sum_bool, add_comm] using congrArg (fun t : ℝ => (t : ℂ)) hsum
    have hder := congrArg (fun f : ℂ → ℂ => fderiv ℝ f (c x)) he
    rw [fderiv_fun_add (hd false) (hd true)] at hder
    have h1 := congrArg (fun d : ℂ →L[ℝ] ℂ => d 1) hder
    have hI := congrArg (fun d : ℂ →L[ℝ] ℂ => d Complex.I) hder
    simp only [ContinuousLinearMap.add_apply, fderiv_const_apply,
      ContinuousLinearMap.zero_apply] at h1 hI
    simp only [chartDbarWeight, chartDbar]
    change (_ + Complex.I * _) / 2 + (_ + Complex.I * _) / 2 = 0
    linear_combination h1 / 2 + Complex.I * hI / 2
  have hpartition_false_coefficient (p : E) (U : Opens E) (hp : p ∈ U)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p U hp))
      (h : HolOn (overlapOpen p U)) (a x : E)
      (hx : x ∈ (extChartAt 𝓘(ℂ) a).source) (hU : x ∈ U) :
      (∑ j : Bool, if hxj : x ∈ (actualPunctureCechCover p U hp).opens j then
        (actualTwoOpenOneCochain p U hp h false j).1 ⟨x, hU, hxj⟩ *
          chartDbarWeight a (P.weight j) x else 0) =
        if hV : x ∈ puncturedOpen p then
          -h.1 ⟨x, hU, hV⟩ * chartDbarWeight a (P.weight false) x else 0 := by
    classical
    rw [Fintype.sum_bool]
    have hd := hpartition_dbar_sum p U hp P a x hx
    by_cases hV : x ∈ puncturedOpen p
    · simp only [actualPunctureCechCover, Bool.false_eq_true, ↓reduceIte,
        actualTwoOpenOneCochain, hU, hV, Submodule.coe_zero, Pi.zero_apply,
        zero_mul, add_zero, dite_true]
      linear_combination h.1 ⟨x, hU, hV⟩ * hd
    · simp [actualPunctureCechCover, actualTwoOpenOneCochain, hU, hV]
  have hpartition_true_coefficient (p : E) (U : Opens E) (hp : p ∈ U)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p U hp))
      (h : HolOn (overlapOpen p U)) (a x : E) (hV : x ∈ puncturedOpen p) :
      (∑ j : Bool, if hxj : x ∈ (actualPunctureCechCover p U hp).opens j then
        (actualTwoOpenOneCochain p U hp h true j).1 ⟨x, hV, hxj⟩ *
          chartDbarWeight a (P.weight j) x else 0) =
        if hU : x ∈ U then
          -h.1 ⟨x, hU, hV⟩ * chartDbarWeight a (P.weight false) x else 0 := by
    classical
    simp [Fintype.sum_bool, actualPunctureCechCover, actualTwoOpenOneCochain,
      hV, HolOn.restrict]
  have hmul_test (Ω : Opens ℂ) (φ : TestFunction Ω ℂ ⊤)
      (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f Ω) :
      ∃ ψ : TestFunction Ω ℂ ⊤, ∀ z, ψ z = φ z * f z := by
    have hs : ContDiff ℝ ∞ (fun z => φ z * f z) := by
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hz : z ∈ tsupport (φ : ℂ → ℂ)
      · exact φ.contDiff.contDiffAt.mul
          ((hf z (φ.tsupport_subset hz)).contDiffAt.restrict_scalars ℝ)
      · have he : (fun w => φ w * f w) =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
          filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hz] with w hw
          simp [hw]
        exact contDiffAt_const.congr_of_eventuallyEq he
    refine ⟨⟨fun z => φ z * f z, hs, φ.hasCompactSupport.mul_right,
      (tsupport_mul_subset_left).trans φ.tsupport_subset⟩, ?_⟩
    intro z
    rfl
  have hpartitionTest (p : E) (hp : p ∈ chartSourceOpen p)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p (chartSourceOpen p) hp))
      (h : HolOn (overlapOpen p (chartSourceOpen p))) :
      ∃ ψ : TestFunction (actualChartTestOpen p) ℂ ⊤, ∀ z,
        ψ z = -dbar (fun w => (actualChartCutoffTest p (P.weight false)
          (P.smoothWeight false) (P.supportWeight false) w : ℂ)) z * actualChartOverlapValue p h z := by
    let Ω := actualChartTestOpen p
    let z₀ := (chartAt ℂ p) p
    let χ := actualChartCutoffTest p (P.weight false) (P.smoothWeight false) (P.supportWeight false)
    let χc : TestFunction Ω ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM χ
    have hone : (χc : ℂ → ℂ) =ᶠ[𝓝 z₀] fun _ => (1 : ℂ) := by
      have ho := actualChartCutoffTest_one_near p (P.weight false) (P.smoothWeight false)
        (P.supportWeight false) (hpartition_one_near p (chartSourceOpen p) hp P)
      filter_upwards [ho] with z hz
      change (χ z : ℂ) = 1
      rw [hz]
      norm_num
    have hzero : (testDbar Ω χc : ℂ → ℂ) =ᶠ[𝓝 z₀] fun _ => (0 : ℂ) := by
      filter_upwards [hone.fderiv (𝕜 := ℝ)] with z hz
      simp [testDbar_apply, dbar, hz]
    have hnot : z₀ ∉ tsupport (testDbar Ω χc : ℂ → ℂ) :=
      notMem_tsupport_iff_eventuallyEq.mpr hzero
    let Ω' : Opens ℂ := ⟨(Ω : Set ℂ) \ {z₀}, Ω.isOpen.sdiff isClosed_singleton⟩
    let δ : TestFunction Ω' ℂ ⊤ := ⟨testDbar Ω χc, (testDbar Ω χc).contDiff,
      (testDbar Ω χc).hasCompactSupport, by
        intro z hz
        exact ⟨(testDbar Ω χc).tsupport_subset hz, fun he => hnot (he ▸ hz)⟩⟩
    have hhol : AnalyticOnNhd ℂ (actualChartOverlapValue p h) Ω' := by
      intro z hz
      exact actualChartOverlapValue_analyticAt p h z (by simpa [Ω, actualChartTestOpen] using hz.1) hz.2
    obtain ⟨ψ, hψ⟩ := hmul_test Ω' δ (actualChartOverlapValue p h) hhol
    refine ⟨-(TestFunction.monoCLM ℂ ψ : TestFunction Ω ℂ ⊤), ?_⟩
    intro z
    have hsub : Ω' ≤ Ω := fun z hz => hz.1
    simp only [FunLike.coe_neg, Pi.neg_apply, TestFunction.monoCLM_apply, le_refl,
      hsub, and_self, ite_true, hψ]
    change -(testDbar Ω χc z * actualChartOverlapValue p h z) = _
    rw [testDbar_apply]
    exact (neg_mul _ _).symm
  have hpartitionRepresentation (p : E) (hp : p ∈ chartSourceOpen p)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p (chartSourceOpen p) hp))
      (h : HolOn (overlapOpen p (chartSourceOpen p))) :
      ∃ ψ : TestFunction (actualChartTestOpen p) ℂ ⊤,
        (∀ z, ψ z = -dbar (fun w => (actualChartCutoffTest p (P.weight false)
          (P.smoothWeight false) (P.supportWeight false) w : ℂ)) z * actualChartOverlapValue p h z) ∧
        actualChartTestFormExtension p ψ =
          cechToDolbeault (actualPunctureCechCover p (chartSourceOpen p) hp) P
            (actualTwoOpenCocycle p (chartSourceOpen p) hp h) := by
    obtain ⟨ψ, hψ⟩ := hpartitionTest p hp P h
    let c := extChartAt 𝓘(ℂ) p
    let χ := actualChartCutoffTest p (P.weight false) (P.smoothWeight false) (P.supportWeight false)
    let V := actualPunctureCechCover p (chartSourceOpen p) hp
    let g := actualTwoOpenCocycle p (chartSourceOpen p) hp h
    let α := cechToDolbeault V P g
    have hχ (x : E) (hx : x ∈ c.source) :
        dbar (fun w => (χ w : ℂ)) (c x) = chartDbarWeight p (P.weight false) x := by
      have he : (fun w => (χ w : ℂ)) =ᶠ[𝓝 (c x)]
          (fun w => (P.weight false (c.symm w) : ℂ)) := by
        filter_upwards [(isOpen_extChartAt_target p).mem_nhds (c.map_source hx)] with w hw
        change ((if w ∈ c.target then P.weight false (c.symm w) else 0 : ℝ) : ℂ) = _
        rw [ite_eq_left hw]
      unfold dbar chartDbarWeight chartDbar
      rw [he.fderiv_eq]
    have hcoef (x : E) (hx : x ∈ c.source) : ψ (c x) = α.1 p x := by
      have hxU : x ∈ chartSourceOpen p := by simpa [c, chartSourceOpen] using hx
      have hv := cechToDolbeault_local V P p x hx g false hxU
      rw [hv]
      change ψ (c x) = chartCechDbarCoefficient V p P.weight g false x hxU
      unfold chartCechDbarCoefficient
      change ψ (c x) = (∑ j : Bool, if hxj : x ∈ V.opens j then
        (actualTwoOpenOneCochain p (chartSourceOpen p) hp h false j).1 ⟨x, hxU, hxj⟩ *
          chartDbarWeight p (P.weight j) x else 0)
      rw [hpartition_false_coefficient p (chartSourceOpen p) hp P h p x hx hxU, hψ (c x)]
      by_cases hV : x ∈ puncturedOpen p
      · rw [dite_eq_left hV]
        have hne : c x ≠ (chartAt ℂ p) p := by
          intro he
          have he' : (chartAt ℂ p) x = (chartAt ℂ p) p := by simpa [c] using he
          exact hV ((chartAt ℂ p).injOn hxU hp he')
        have hv : actualChartOverlapValue p h (c x) = h.1 ⟨x, hxU, hV⟩ := by
          rw [actualChartOverlapValue_of_target_ne p h (c x)
            (by simpa [c] using c.map_source hx) hne]
          apply congrArg h.1
          apply Subtype.ext
          simpa [c] using c.left_inv hx
        rw [hv]
        change -dbar (fun w => (χ w : ℂ)) (c x) * h.1 ⟨x, hxU, hV⟩ = _
        rw [hχ x hx]
        ring
      · rw [dite_eq_right hV]
        have he : x = p := not_ne_iff.mp hV
        subst x
        simp [actualChartOverlapValue, c]
    refine ⟨ψ, hψ, ?_⟩
    apply Subtype.ext
    funext b x
    by_cases hb : x ∈ (extChartAt 𝓘(ℂ) b).source
    · by_cases hx : x ∈ c.source
      · change (if x ∈ c.source ∧ x ∈ (extChartAt 𝓘(ℂ) b).source then _ else 0) = _
        rw [ite_eq_left ⟨hx, hb⟩, hcoef x hx]
        exact (α.property.2.2 p b x hx hb).symm
      · have hxp : x ≠ p := by
          rintro rfl
          exact hx (mem_extChartAt_source x)
        have hxV : x ∈ puncturedOpen p := hxp
        have hv := cechToDolbeault_local V P b x hb g true hxV
        change (if x ∈ c.source ∧ x ∈ (extChartAt 𝓘(ℂ) b).source then _ else 0) = α.1 b x
        rw [ite_eq_right (fun h => hx h.1), hv]
        change 0 = (∑ j : Bool, if hxj : x ∈ V.opens j then
          (actualTwoOpenOneCochain p (chartSourceOpen p) hp h true j).1 ⟨x, hxV, hxj⟩ *
            chartDbarWeight b (P.weight j) x else 0)
        rw [hpartition_true_coefficient p (chartSourceOpen p) hp P h b x hxV]
        have hn : x ∉ chartSourceOpen p := by simpa [chartSourceOpen, c] using hx
        rw [dite_eq_right hn]
    · exact ((actualChartTestFormExtension p ψ).property.1 b x hb).trans (α.property.1 b x hb).symm
  have hpartitionContour (p : E) (hp : p ∈ chartSourceOpen p)
      (P : SubordinateSmoothPartition (actualPunctureCechCover p (chartSourceOpen p) hp))
      (h : HolOn (overlapOpen p (chartSourceOpen p)))
      (ψ : TestFunction (actualChartTestOpen p) ℂ ⊤)
      (hψ : ∀ z, ψ z = -dbar (fun w => (actualChartCutoffTest p (P.weight false)
          (P.smoothWeight false) (P.supportWeight false) w : ℂ)) z * actualChartOverlapValue p h z)
      (s : ActualCanonicalSection E) (R : ℝ) (hR : 0 < R)
      (htarget : Metric.closedBall ((chartAt ℂ p) p) R ⊆ (chartAt ℂ p).target) :
      (∫ z : ℂ, (2 * Complex.I) * ψ z *
        chartCanonicalCoefficient p ((extChartAt 𝓘(ℂ) p).symm z) s) =
        actualOverlapContourPairing p R hR htarget h s := by
    rw [← actualChartCutoffContour p (P.weight false) (P.smoothWeight false)
      (P.supportWeight false) (hpartition_one_near p (chartSourceOpen p) hp P) h s R hR htarget]
    apply integral_congr_ae
    filter_upwards [] with z
    by_cases hz : z ∈ (extChartAt 𝓘(ℂ) p).target
    · have he : chartCanonicalCoefficient p ((extChartAt 𝓘(ℂ) p).symm z) s =
          actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ)) := by
        rw [chartCanonicalCoefficient_inverseChartDerivative p _
          ((extChartAt 𝓘(ℂ) p).map_target hz) s,
          inverseChartTangentFrame_eq_trivialization p _ ((extChartAt 𝓘(ℂ) p).map_target hz)]
        have hv := actualLocalOneForm_eq_global_in_chart s p
          ((extChartAt 𝓘(ℂ) p).symm z) 1
          (show (extChartAt 𝓘(ℂ) p).symm z ∈ (chartAt ℂ p).source from by
            simpa using (extChartAt 𝓘(ℂ) p).map_target hz)
        simpa [actualOneForm, (chartAt ℂ p).right_inv (show z ∈ (chartAt ℂ p).target from by simpa using hz)] using hv.symm
      rw [hψ z, he]
      ring
    · have hzero := ψ.zero_on_compl hz
      have he : dbar (fun w => (actualChartCutoffTest p (P.weight false)
          (P.smoothWeight false) (P.supportWeight false) w : ℂ)) z = 0 := by
        let χ := actualChartCutoffTest p (P.weight false) (P.smoothWeight false) (P.supportWeight false)
        simpa only [testDbar_apply, TestFunction.postcompCLM_apply, Complex.ofRealCLM_apply, Pi.zero_apply, Function.comp_def, χ] using
          (testDbar (actualChartTestOpen p)
            (TestFunction.postcompCLM Complex.ofRealCLM χ)).zero_on_compl hz
      simp [hzero, he]
  intro p c hc
  let U := chartSourceOpen p
  have hp : p ∈ U := mem_chart_source ℂ p
  let V := actualPunctureCechCover p U hp
  let P : SubordinateSmoothPartition V := Classical.choice (exists_subordinateSmoothPartition V)
  let h := actualChartPoleOverlapRepresentative p c
  let g := actualTwoOpenCocycle p U hp h
  let α := cechToDolbeault V P g
  have hr : α ∈ (dolbeaultDbar (E := E)).range := by
    by_contra hn
    obtain ⟨T, hT, hTα⟩ := hseparate (dolbeaultDbar (E := E)).range
      dolbeaultDbar_range_isClosed α hn
    obtain ⟨s, hs⟩ := hglobalSection_localRepresentation T
      (fun f => hT (dolbeaultDbar f) ⟨f, rfl⟩)
    obtain ⟨ψ, hψ, hα⟩ := hpartitionRepresentation p hp P h
    apply hTα
    change T (cechToDolbeault V P g) = 0
    rw [← hα, hs p ψ, hpartitionContour p hp P h ψ hψ s
      (actualChartResidueRadius p) (actualChartResidueRadius_pos p)
      (actualChartResidueRadius_target p)]
    change (∮ z in C((chartAt ℂ p) p, actualChartResidueRadius p),
      actualChartOverlapValue p (actualChartPoleOverlapRepresentative p c) z *
        actualLocalOneForm s p z (fun _ : Fin 1 => (1 : ℂ))) = 0
    rw [actualChartPoleOverlapRepresentative_circleIntegral s p c
      (actualChartResidueRadius p) (actualChartResidueRadius_pos p)
      (actualChartResidueRadius_target p)]
    calc
      c * (2 * Real.pi * Complex.I) * actualCanonicalEvaluation p s =
          (2 * Real.pi * Complex.I) * (c * actualCanonicalEvaluation p s) := by ring
      _ = 0 := by rw [hc s, mul_zero]
  have hgzero : classOf V g = 0 := by
    apply actualFiniteDolbeaultInjectivity E V P
    rw [map_zero, cechDolbeaultComparison_classOf]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hr
  apply (actualTwoOpenCechComparison_bijective p U hp).1
  rw [map_zero, scalarCechBoundary_eq_overlap_representative,
    actualTwoOpenCechComparison_mkQ]
  exact hgzero

#print axioms actualPointMittagLefflerDetection
end CanonicalDimensionTwo
