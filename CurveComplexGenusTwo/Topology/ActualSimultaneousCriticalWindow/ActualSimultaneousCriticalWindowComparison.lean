import CurveComplexGenusTwo.CWHurewicz.ExcisionDifferentialTransport
import CurveComplexGenusTwo.CWHurewicz.PairExactnessInterface
import CurveComplexGenusTwo.CWHurewicz.PairHomotopyInvariance
import CurveComplexGenusTwo.CWHurewicz.PairNaturality
import CurveComplexGenusTwo.CWHurewicz.SphereHomology.SphereBaseHelpers
import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.Algebra.Exact.Sequence
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Dynamics.Flow
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.IntegralCurve.ExistUnique
import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorField.Pullback
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Topology.DiscreteSubset
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Topology.Instances.Complex
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Separation.Regular
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualCriticalWindowData
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseUphillIntegralCurve
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseCompleteContinuousFlow
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseUphillContinuity
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseNormalizedRegularBand
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualFiniteDisjointChartBalls
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseNormalizedAwayFromCriticalCharts
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualPublicPairHomeomorphTransport
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualAllDegreeExcision


set_option backward.isDefEq.respectTransparency false

open scoped ContDiff
open Set

private def saddleCircleField (z : ℂ) : ℂ :=
  ⟨z.re * z.im ^ 2, -(z.im * z.re ^ 2)⟩

private theorem saddleCircleField_smooth : ContDiff ℝ ∞ saddleCircleField := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  have h : ContDiff ℝ ∞ (fun z : ℂ =>
      ((z.re * z.im ^ 2 : ℝ) : ℂ) + ((-(z.im * z.re ^ 2) : ℝ) : ℂ) * Complex.I) :=
    (Complex.ofRealCLM.contDiff.comp (hr.mul (hi.pow 2))).add
      ((Complex.ofRealCLM.contDiff.comp (hi.mul (hr.pow 2)).neg).mul contDiff_const)
  convert h using 1
  funext z
  apply Complex.ext <;> simp only [saddleCircleField, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] <;> ring

private theorem radiusSq_fderiv (z w : ℂ) :
    fderiv ℝ (fun u : ℂ => u.re ^ 2 + u.im ^ 2) z w =
      2 * z.re * w.re + 2 * z.im * w.im := by
  have h := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  change (fderiv ℝ _ z) w = _
  simpa [Pi.add_def, Pi.sub_def] using congrArg (fun L : ℂ →L[ℝ] ℝ => L w) h.fderiv

private theorem saddle_fderiv (z w : ℂ) :
    fderiv ℝ (actualCriticalWindowQuadratic 1) z w =
      2 * z.re * w.re - 2 * z.im * w.im := by
  have h := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).sub
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  have hq : actualCriticalWindowQuadratic 1 =
      fun u : ℂ => u.re ^ 2 - u.im ^ 2 := by
    funext u
    simp [actualCriticalWindowQuadratic]
  rw [hq]
  simpa [Pi.add_def, Pi.sub_def] using congrArg (fun L : ℂ →L[ℝ] ℝ => L w) h.fderiv

private theorem saddleCircleField_radial (z : ℂ) :
    fderiv ℝ (fun u : ℂ => u.re ^ 2 + u.im ^ 2) z (saddleCircleField z) = 0 := by
  rw [radiusSq_fderiv]
  simp only [saddleCircleField]
  ring

private theorem saddleCircleField_energy (z : ℂ) :
    fderiv ℝ (actualCriticalWindowQuadratic 1) z (saddleCircleField z) =
      4 * z.re ^ 2 * z.im ^ 2 := by
  rw [saddle_fderiv]
  simp only [saddleCircleField]
  ring

private theorem saddleCircleField_energy_radius (z : ℂ) :
    fderiv ℝ (actualCriticalWindowQuadratic 1) z (saddleCircleField z) =
      (z.re ^ 2 + z.im ^ 2) ^ 2 - (actualCriticalWindowQuadratic 1 z) ^ 2 := by
  rw [saddleCircleField_energy]
  simp only [actualCriticalWindowQuadratic, show (1 : Fin 3) ≠ 0 by decide,
    ↓reduceIte]
  ring

private theorem quadratic_smooth (k : Fin 3) :
    ContDiff ℝ ∞ (actualCriticalWindowQuadratic k) := by
  have hr : ContDiff ℝ ∞ (fun z : ℂ => z.re) := Complex.reCLM.contDiff
  have hi : ContDiff ℝ ∞ (fun z : ℂ => z.im) := Complex.imCLM.contDiff
  unfold actualCriticalWindowQuadratic
  split_ifs
  · exact (hr.pow 2).add (hi.pow 2)
  · exact (hr.pow 2).sub (hi.pow 2)
  · exact ((hr.pow 2).add (hi.pow 2)).neg

private theorem collar_index_one (k : Fin 3) (z : ℂ)
    (h : |actualCriticalWindowQuadratic k z| < z.re ^ 2 + z.im ^ 2) : k = 1 := by
  have hn : 0 ≤ z.re ^ 2 + z.im ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
  fin_cases k
  · change |z.re ^ 2 + z.im ^ 2| < z.re ^ 2 + z.im ^ 2 at h
    rw [abs_of_nonneg hn] at h
    exact (lt_irrefl _ h).elim
  · rfl
  · change |-(z.re ^ 2 + z.im ^ 2)| < z.re ^ 2 + z.im ^ 2 at h
    rw [abs_neg, abs_of_nonneg hn] at h
    exact (lt_irrefl _ h).elim

private theorem saddleCircleField_uphill (k : Fin 3) (z : ℂ)
    (h : |actualCriticalWindowQuadratic k z| < z.re ^ 2 + z.im ^ 2) :
    0 < fderiv ℝ (actualCriticalWindowQuadratic k) z (saddleCircleField z) := by
  have hk := collar_index_one k z h
  subst k
  rw [saddleCircleField_energy_radius]
  have hp := abs_lt.mp h
  nlinarith [mul_pos (sub_pos.mpr hp.2) (by linarith [hp.1] :
    0 < z.re ^ 2 + z.im ^ 2 + actualCriticalWindowQuadratic 1 z)]

private theorem normSq_coords (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply, pow_two]

private theorem saddleCircleField_sphere_uphill (k : Fin 3) (r ε : ℝ) (z : ℂ)
    (hε : ε < r ^ 2) (hz : ‖z‖ = r)
    (hq : |actualCriticalWindowQuadratic k z| ≤ ε) :
    0 < fderiv ℝ (actualCriticalWindowQuadratic k) z (saddleCircleField z) := by
  apply saddleCircleField_uphill
  calc |actualCriticalWindowQuadratic k z| ≤ ε := hq
    _ < r ^ 2 := hε
    _ = z.re ^ 2 + z.im ^ 2 := by rw [← hz, normSq_coords]

private theorem saddleCircleField_scaled_radial (z : ℂ) (a : ℝ) :
    fderiv ℝ (fun u : ℂ => u.re ^ 2 + u.im ^ 2) z (a • saddleCircleField z) = 0 := by
  rw [map_smul, saddleCircleField_radial, smul_zero]

private theorem saddleCircleField_scaled_uphill (k : Fin 3) (z : ℂ) (a : ℝ)
    (ha : 0 < a)
    (h : |actualCriticalWindowQuadratic k z| < z.re ^ 2 + z.im ^ 2) :
    0 < fderiv ℝ (actualCriticalWindowQuadratic k) z (a • saddleCircleField z) := by
  rw [map_smul, smul_eq_mul]
  exact mul_pos ha (saddleCircleField_uphill k z h)


open scoped Manifold Bundle Topology
open Bundle Filter

private noncomputable def saddleChartField
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (c : OpenPartialHomeomorph E ℂ) : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x :=
  VectorField.mpullback 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c saddleCircleField

private theorem smoothChart_mfderiv_invertible
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (x : E) (hx : x ∈ c.source) :
    (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x).IsInvertible := by
  have h : c.MDifferentiable 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) :=
    ⟨hc.mdifferentiableOn (by simp), hci.mdifferentiableOn (by simp)⟩
  exact ⟨h.mfderiv hx, rfl⟩

private theorem saddleChartField_smooth_on
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target) :
    ContMDiffOn 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (saddleChartField c x)) c.source := by
  intro x hx
  have hV : ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ).tangent ∞
      (fun z : ℂ => (⟨z, saddleCircleField z⟩ : TangentBundle 𝓘(ℝ,ℂ) ℂ)) (c x) :=
    contMDiffAt_vectorSpace_iff_contDiffAt.mpr saddleCircleField_smooth.contDiffAt
  exact (hV.mpullback_vectorField_preimage
    ((hc x hx).contMDiffAt (c.open_source.mem_nhds hx))
    (smoothChart_mfderiv_invertible c hc hci x hx) (by simp)).contMDiffWithinAt

private theorem saddleChartField_derivative
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (x : E) (hx : x ∈ c.source) :
    (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x) (saddleChartField c x) =
      saddleCircleField (c x) := by
  obtain ⟨e, he⟩ := smoothChart_mfderiv_invertible c hc hci x hx
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x)
    ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c x).inverse (saddleCircleField (c x))) = _
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact e.apply_symm_apply _


private theorem chartField_scalar_derivative
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (f : ℂ → ℝ) (hf : ContDiff ℝ ∞ f) (G : E → ℝ)
    (hG : EqOn G (fun x => f (c x)) c.source) (x : E) (hx : x ∈ c.source) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (G x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G x) (saddleChartField c x)) =
      fderiv ℝ f (c x) (saddleCircleField (c x)) := by
  have hc' := ((hc x hx).contMDiffAt (c.open_source.mem_nhds hx)).mdifferentiableAt
    (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hf' : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ) f (c x) := hf.contMDiff.contMDiffAt.mdifferentiableAt (by simp : (∞ : WithTop ℕ∞) ≠ 0)
  have hcomp := mfderiv_comp_apply x hf' hc' (saddleChartField c x)
  have heq : (f ∘ c) =ᶠ[𝓝 x] G := by
    filter_upwards [c.open_source.mem_nhds hx] with y hy
    exact (hG hy).symm
  rw [heq.mfderiv_eq] at hcomp
  rw [saddleChartField_derivative c hc hci x hx, mfderiv_eq_fderiv] at hcomp
  exact hcomp

private theorem saddleChartField_actual_energy
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (F : E → ℝ) (v : ℝ) (k : Fin 3)
    (hnormal : ∀ x ∈ c.source, F x = v + actualCriticalWindowQuadratic k (c x))
    (x : E) (hx : x ∈ c.source)
    (hsmall : |F x - v| < ‖c x‖ ^ 2) :
    0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (saddleChartField c x)) := by
  rw [chartField_scalar_derivative c hc hci (fun z => v + actualCriticalWindowQuadratic k z)
    (contDiff_const.add (quadratic_smooth k)) F hnormal x hx]
  have hf : DifferentiableAt ℝ (actualCriticalWindowQuadratic k) (c x) :=
    (quadratic_smooth k).differentiable (by simp) (c x)
  rw [fderiv_const_add v]
  apply saddleCircleField_uphill
  rw [hnormal x hx, add_sub_cancel_left, normSq_coords] at hsmall
  exact hsmall

private theorem saddleChartField_actual_radial
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (x : E) (hx : x ∈ c.source) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (‖c x‖ ^ 2))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c y‖ ^ 2) x) (saddleChartField c x)) = 0 := by
  have h := chartField_scalar_derivative c hc hci
    (fun z : ℂ => z.re ^ 2 + z.im ^ 2)
    ((Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2))
    (fun y => ‖c y‖ ^ 2) (fun y _ => normSq_coords (c y)) x hx
  rw [h, saddleCircleField_radial]

private theorem supported_saddleChartField_smooth
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (hci : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c.symm c.target)
    (b : E → ℝ) (hb : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b)
    (hs : tsupport b ⊆ c.source) :
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (b x • saddleChartField c x)) := by
  exact ContMDiffOn.smul_section_of_tsupport hb.contMDiffOn c.open_source hs
    (saddleChartField_smooth_on c hc hci)


private theorem compact_manifold_plateau
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (K U : Set E) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ b : E → ℝ, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      tsupport b ⊆ U ∧ (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧ ∀ x ∈ K, b x = 1 := by
  obtain ⟨V, hVopen, hKV, hVU⟩ := normal_exists_closure_subset hK.isClosed hU hKU
  obtain ⟨W, hWopen, hVW, hWU⟩ :=
    normal_exists_closure_subset isClosed_closure hU hVU
  obtain ⟨b, hb, hbounds, hs, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff
      (I := 𝓘(ℝ,ℂ)) hWopen isClosed_closure hVW
  refine ⟨b, hb, ?_, (fun x => hbounds (mem_range_self x)), ?_⟩
  · change closure (Function.support b) ⊆ U
    rw [hs]
    exact hWU
  · intro x hx
    exact (hone x).mp (subset_closure (hKV hx))


private theorem chart_sphere_compact
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (r : ℝ) (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target) :
    IsCompact {x : E | x ∈ c.source ∧ ‖c x‖ = r} := by
  have heq : {x : E | x ∈ c.source ∧ ‖c x‖ = r} =
      c.symm '' Metric.sphere (0 : ℂ) r := by
    ext x
    constructor
    · intro hx
      exact ⟨c x, by simpa only [Metric.mem_sphere, dist_zero_right] using hx.2,
        c.left_inv hx.1⟩
    · rintro ⟨z, hz, rfl⟩
      have ht := hball (Metric.sphere_subset_closedBall hz)
      exact ⟨c.symm.map_source ht, by
        rw [c.right_inv ht]
        simpa only [Metric.mem_sphere, dist_zero_right] using hz⟩
  rw [heq]
  exact (isCompact_sphere (0 : ℂ) r).image_of_continuousOn
    (c.symm.continuousOn.mono (fun z hz => hball (Metric.sphere_subset_closedBall hz)))

private theorem chart_sphere_has_supported_collar
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (c : OpenPartialHomeomorph E ℂ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target) :
    ∃ b : E → ℝ, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      tsupport b ⊆ {x | x ∈ c.source ∧ r / 2 < ‖c x‖ ∧ ‖c x‖ < 2 * r} ∧
      ∀ x, x ∈ c.source → ‖c x‖ = r → b x = 1 := by
  let K := {x : E | x ∈ c.source ∧ ‖c x‖ = r}
  let U := {x : E | x ∈ c.source ∧ r / 2 < ‖c x‖ ∧ ‖c x‖ < 2 * r}
  have hU : IsOpen U := c.isOpen_inter_preimage
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hKU : K ⊆ U := by
    rintro x ⟨hx, he⟩
    exact ⟨hx, by rw [he]; linarith, by rw [he]; linarith⟩
  obtain ⟨b, hb, hs, hbounds, hone⟩ := compact_manifold_plateau K U
    (chart_sphere_compact c r hball) hU hKU
  exact ⟨b, hb, hbounds, hs, fun x hx he => hone x ⟨hx, he⟩⟩

private noncomputable def collarPatchedField
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (b : E → E → ℝ)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) :
    ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x := fun x =>
  (1 - ∑ q ∈ S, b q x) • X x + ∑ q ∈ S, b q x • saddleChartField (c q) x

private theorem collarPatchedField_smooth
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (b : E → E → ℝ)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (hc : ∀ q ∈ S, ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hb : ∀ q ∈ S, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (b q))
    (hs : ∀ q ∈ S, tsupport (b q) ⊆ (c q).source) :
    ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (collarPatchedField S c b X x)) := by
  apply ContMDiff.add_section
  · exact (contMDiff_const.sub (ContMDiff.sum hb)).smul_section hX
  · exact ContMDiff.sum_section (fun q hq =>
      supported_saddleChartField_smooth (c q) (hc q hq).1 (hc q hq).2
        (b q) (hb q hq) (hs q hq))

private theorem collar_unique_nonzero
    {E : Type} [TopologicalSpace E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ)
    (b : E → E → ℝ)
    (hs : ∀ q ∈ S, tsupport (b q) ⊆
      {x | x ∈ (c q).source ∧ ρ q / 2 < ‖c q x‖ ∧ ‖c q x‖ < 2 * ρ q})
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (2 * ρ q)))
    (p : E) (hp : p ∈ S) (x : E) (hbp : b p x ≠ 0) :
    ∀ q ∈ S, q ≠ p → b q x = 0 := by
  intro q hq hqp
  by_contra hbq
  have hpx := hs p hp (subset_tsupport (b p) hbp)
  have hqx := hs q hq (subset_tsupport (b q) hbq)
  exact Set.disjoint_left.mp (hd hp hq hqp.symm)
    ⟨hpx.1, hpx.2.2.le⟩ ⟨hqx.1, hqx.2.2.le⟩

private theorem collarPatchedField_eq_single
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (b : E → E → ℝ)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (p : E) (hp : p ∈ S) (x : E)
    (hb : ∀ q ∈ S, q ≠ p → b q x = 0) :
    collarPatchedField S c b X x =
      (1 - b p x) • X x + b p x • saddleChartField (c p) x := by
  classical
  have hsum : ∑ q ∈ S, b q x = b p x :=
    Finset.sum_eq_single p hb (fun hn => (hn hp).elim)
  have hvec : ∑ q ∈ S, b q x • saddleChartField (c q) x =
      b p x • saddleChartField (c p) x := by
    apply Finset.sum_eq_single p
    · intro q hq hqp
      rw [hb q hq hqp, zero_smul]
    · intro hn
      exact (hn hp).elim
  simp only [collarPatchedField, hsum, hvec]

private theorem collarPatchedField_energy_positive
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ)
    (k : E → Fin 3) (b : E → E → ℝ)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x) (F : E → ℝ) (v ε : ℝ)
    (hc : ∀ q ∈ S, ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hn : ∀ q ∈ S, ∀ x ∈ (c q).source,
      F x = v + actualCriticalWindowQuadratic (k q) (c q x))
    (hr : ∀ q ∈ S, 0 < ρ q ∧ ε < (ρ q / 2) ^ 2)
    (hb : ∀ q ∈ S, ∀ x, 0 ≤ b q x ∧ b q x ≤ 1)
    (hs : ∀ q ∈ S, tsupport (b q) ⊆
      {x | x ∈ (c q).source ∧ ρ q / 2 < ‖c q x‖ ∧ ‖c q x‖ < 2 * ρ q})
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (2 * ρ q)))
    (x : E) (hx : |F x - v| ≤ ε)
    (hX : 0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) :
    0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (collarPatchedField S c b X x)) := by
  classical
  by_cases hall : ∀ q ∈ S, b q x = 0
  · have hf : collarPatchedField S c b X x = X x := by
      simp only [collarPatchedField]
      have hz : (∑ q ∈ S, b q x • saddleChartField (c q) x) = 0 := by
        apply Finset.sum_eq_zero
        intro q hq
        rw [hall q hq, zero_smul]
      rw [Finset.sum_eq_zero (fun q hq => hall q hq), hz]
      simp
    simpa only [hf] using hX
  · push_neg at hall
    obtain ⟨p, hp, hbp⟩ := hall
    have hpx := hs p hp (subset_tsupport (b p) hbp)
    have hsmall : |F x - v| < ‖c p x‖ ^ 2 := by
      have hrp := hr p hp
      have hnpos := norm_nonneg (c p x)
      have hsq : (ρ p / 2) ^ 2 < ‖c p x‖ ^ 2 :=
        (sq_lt_sq₀ (div_nonneg hrp.1.le (by norm_num)) hnpos).mpr hpx.2.1
      exact hx.trans_lt (hrp.2.trans hsq)
    have hW := saddleChartField_actual_energy (c p) (hc p hp).1 (hc p hp).2
      F v (k p) (hn p hp) x hpx.1 hsmall
    rw [collarPatchedField_eq_single S c b X p hp x
      (collar_unique_nonzero S c ρ b hs hd p hp x hbp)]
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr (hb p hp x).2) hX.le)
      (mul_pos (lt_of_le_of_ne (hb p hp x).1 (Ne.symm hbp)) hW)

private theorem collarPatchedField_sphere_radial
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ)
    (b : E → E → ℝ) (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hc : ∀ q ∈ S, ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hs : ∀ q ∈ S, tsupport (b q) ⊆
      {x | x ∈ (c q).source ∧ ρ q / 2 < ‖c q x‖ ∧ ‖c q x‖ < 2 * ρ q})
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (2 * ρ q)))
    (hone : ∀ q ∈ S, ∀ x, x ∈ (c q).source → ‖c q x‖ = ρ q → b q x = 1)
    (p : E) (hp : p ∈ S) (x : E) (hxs : x ∈ (c p).source) (hxr : ‖c p x‖ = ρ p) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (‖c p x‖ ^ 2))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c p y‖ ^ 2) x)
        (collarPatchedField S c b X x)) = 0 := by
  have hbp := hone p hp x hxs hxr
  rw [collarPatchedField_eq_single S c b X p hp x
    (collar_unique_nonzero S c ρ b hs hd p hp x (by rw [hbp]; norm_num)),
    hbp, sub_self, zero_smul, zero_add, one_smul]
  exact saddleChartField_actual_radial (c p) (hc p hp).1 (hc p hp).2 x hxs


private theorem chart_annulus_compact
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (l r : ℝ) (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target) :
    IsCompact {x : E | x ∈ c.source ∧ l ≤ ‖c x‖ ∧ ‖c x‖ ≤ r} := by
  have heq : {x : E | x ∈ c.source ∧ l ≤ ‖c x‖ ∧ ‖c x‖ ≤ r} =
      c.symm '' (Metric.closedBall (0 : ℂ) r \ Metric.ball (0 : ℂ) l) := by
    ext x
    constructor
    · intro hx
      refine ⟨c x, ⟨?_, ?_⟩, c.left_inv hx.1⟩
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2.2
      · simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hx.2.1
    · rintro ⟨z, hz, rfl⟩
      have ht := hball hz.1
      refine ⟨c.symm.map_source ht, ?_, ?_⟩ <;> rw [c.right_inv ht]
      · simpa only [Metric.mem_ball, dist_zero_right, not_lt] using hz.2
      · simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1
  rw [heq]
  exact ((isCompact_closedBall (0 : ℂ) r).diff Metric.isOpen_ball).image_of_continuousOn
    (c.symm.continuousOn.mono (fun z hz => hball hz.1))

private theorem chart_sphere_has_supported_open_collar
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (c : OpenPartialHomeomorph E ℂ) (r : ℝ) (hr : 0 < r)
    (hball : Metric.closedBall (0 : ℂ) (2 * r) ⊆ c.target) :
    ∃ b : E → ℝ, ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      tsupport b ⊆ {x | x ∈ c.source ∧ r / 2 < ‖c x‖ ∧ ‖c x‖ < 2 * r} ∧
      ∀ x, x ∈ c.source → 3 * r / 4 ≤ ‖c x‖ → ‖c x‖ ≤ 5 * r / 4 → b x = 1 := by
  let K := {x : E | x ∈ c.source ∧ 3 * r / 4 ≤ ‖c x‖ ∧ ‖c x‖ ≤ 5 * r / 4}
  let U := {x : E | x ∈ c.source ∧ r / 2 < ‖c x‖ ∧ ‖c x‖ < 2 * r}
  have hU : IsOpen U := c.isOpen_inter_preimage
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hKU : K ⊆ U := by
    rintro x ⟨hx, hl, hu⟩
    exact ⟨hx, by linarith, by linarith⟩
  obtain ⟨b, hb, hs, hbounds, hone⟩ := compact_manifold_plateau K U
    (chart_annulus_compact c (3 * r / 4) (5 * r / 4)
      ((Metric.closedBall_subset_closedBall (by linarith)).trans hball)) hU hKU
  exact ⟨b, hb, hbounds, hs, fun x hx hl hu => hone x ⟨hx, hl, hu⟩⟩

private theorem collarPatchedField_collar_radial
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ)
    (b : E → E → ℝ) (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hc : ∀ q ∈ S, ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hs : ∀ q ∈ S, tsupport (b q) ⊆
      {x | x ∈ (c q).source ∧ ρ q / 2 < ‖c q x‖ ∧ ‖c q x‖ < 2 * ρ q})
    (hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (2 * ρ q)))
    (p : E) (hp : p ∈ S) (x : E) (hxs : x ∈ (c p).source) (hbp : b p x = 1) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (‖c p x‖ ^ 2))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c p y‖ ^ 2) x)
        (collarPatchedField S c b X x)) = 0 := by
  rw [collarPatchedField_eq_single S c b X p hp x
    (collar_unique_nonzero S c ρ b hs hd p hp x (by rw [hbp]; norm_num)),
    hbp, sub_self, zero_smul, zero_add, one_smul]
  exact saddleChartField_actual_radial (c p) (hc p hp).1 (hc p hp).2 x hxs

private theorem quadratic_fderiv_zero (k : Fin 3) :
    fderiv ℝ (actualCriticalWindowQuadratic k) 0 = 0 := by
  have hr := (Complex.reCLM.hasFDerivAt (x := 0)).pow 2
  have hi := (Complex.imCLM.hasFDerivAt (x := 0)).pow 2
  fin_cases k
  · change fderiv ℝ (fun z : ℂ => z.re ^ 2 + z.im ^ 2) 0 = 0
    simpa [Pi.add_def] using (hr.add hi).fderiv
  · change fderiv ℝ (fun z : ℂ => z.re ^ 2 - z.im ^ 2) 0 = 0
    simpa [Pi.sub_def] using (hr.sub hi).fderiv
  · change fderiv ℝ (fun z : ℂ => -(z.re ^ 2 + z.im ^ 2)) 0 = 0
    simpa [Pi.add_def, Pi.neg_def] using (hr.add hi).neg.fderiv

private theorem normal_center_derivative_zero
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (F : E → ℝ) (v : ℝ) (k : Fin 3)
    (hnormal : ∀ x ∈ c.source, F x = v + actualCriticalWindowQuadratic k (c x))
    (q : E) (hqs : q ∈ c.source) (hq : c q = 0)
    (w : TangentSpace 𝓘(ℝ,ℂ) q) :
    (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F q))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F q) w) = 0 := by
  let f := fun z => v + actualCriticalWindowQuadratic k z
  have hfc : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ) f (c q) :=
    (contDiff_const.add (quadratic_smooth k)).contMDiff.mdifferentiableAt (by simp)
  have hcc := ((hc q hqs).contMDiffAt (c.open_source.mem_nhds hqs)).mdifferentiableAt
    (by simp)
  have hcomp := mfderiv_comp_apply q hfc hcc w
  have heq : (f ∘ c) =ᶠ[𝓝 q] F := by
    filter_upwards [c.open_source.mem_nhds hqs] with x hx
    exact (hnormal x hx).symm
  rw [heq.mfderiv_eq, mfderiv_eq_fderiv] at hcomp
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F q) w =
    (fderiv ℝ f (c q)) ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) c q) w) at hcomp
  change (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F q) w = 0
  rw [hcomp]
  dsimp only [f]
  rw [fderiv_const_add, hq, quadratic_fderiv_zero, ContinuousLinearMap.zero_apply]


private theorem integral_curve_local_scalar_derivative
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (G : E → ℝ) (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (γ : ℝ → E) (t : ℝ) (hγ : IsMIntegralCurveAt γ X t)
    (hG : MDifferentiableAt 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) :
    HasDerivAt (G ∘ γ)
      ((NormedSpace.fromTangentSpace (𝕜 := ℝ) (G (γ t)))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) (X (γ t)))) t := by
  have hγt : HasMFDerivAt 𝓘(ℝ) 𝓘(ℝ,ℂ) γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t))) := by
    obtain ⟨s, hs, hcurve⟩ := Filter.Eventually.exists_mem hγ
    exact hcurve t (mem_of_mem_nhds hs)
  have hcomp := hG.hasMFDerivAt.comp t hγt
  have hfderiv : HasFDerivAt (G ∘ γ)
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) t := hcomp.hasFDerivAt
  have hderiv : HasDerivAt (G ∘ γ)
      (((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) ∘L
        ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) 1) t :=
    (hasFDerivAt_iff_hasDerivAt (𝕜 := ℝ) (F := ℝ)).mp hfderiv
  have heq : ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) ∘L
      ((1 : ℝ →L[ℝ] ℝ).smulRight (X (γ t)))) 1 =
      (mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) G (γ t)) (X (γ t)) := by simp
  rw [heq] at hderiv
  exact hderiv

private theorem chart_radius_smooth_at
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (x : E) (hx : x ∈ c.source) :
    ContMDiffAt 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ (fun y => ‖c y‖ ^ 2) x := by
  have hg : ContDiff ℝ ∞ (fun z : ℂ => ‖z‖ ^ 2) := by
    have he : (fun z : ℂ => ‖z‖ ^ 2) = (fun z : ℂ => z.re ^ 2 + z.im ^ 2) :=
      funext normSq_coords
    rw [he]
    exact (Complex.reCLM.contDiff.pow 2).add (Complex.imCLM.contDiff.pow 2)
  exact hg.contMDiff.contMDiffAt.comp x
    ((hc x hx).contMDiffAt (c.open_source.mem_nhds hx))

private theorem chart_sphere_flow_invariant
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [T2Space E]
    (c : OpenPartialHomeomorph E ℂ)
    (hc : ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ c c.source)
    (r : ℝ) (hr : 0 < r) (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) X)
    (hrad : ∀ x, x ∈ c.source → 3 * r / 4 < ‖c x‖ → ‖c x‖ < 5 * r / 4 →
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (‖c x‖ ^ 2))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c y‖ ^ 2) x) (X x)) = 0) :
    IsInvariant φ {x : E | x ∈ c.source ∧ ‖c x‖ = r} := by
  intro t x hx
  let γ : ℝ → E := fun s => φ s x
  let V : Set E := {y | y ∈ c.source ∧ 3 * r / 4 < ‖c y‖ ∧ ‖c y‖ < 5 * r / 4}
  let U := γ ⁻¹' V
  let G : ℝ → ℝ := fun s => ‖c (γ s)‖ ^ 2
  have hγcont : Continuous γ := φ.continuous continuous_id continuous_const
  have hVo : IsOpen V := c.isOpen_inter_preimage
    ((isOpen_lt continuous_const continuous_norm).inter
      (isOpen_lt continuous_norm continuous_const))
  have hUo : IsOpen U := hVo.preimage hγcont
  have hder (s : ℝ) (hs : s ∈ U) : HasDerivAt G 0 s := by
    have hd := integral_curve_local_scalar_derivative (fun y => ‖c y‖ ^ 2) X γ s
      ((hcurve x).isMIntegralCurveAt s)
      ((chart_radius_smooth_at c hc (γ s) hs.1).mdifferentiableAt (by simp))
    rw [hrad (γ s) hs.1 hs.2.1 hs.2.2] at hd
    exact hd
  have hVo' : IsOpen (U ∩ G ⁻¹' {r ^ 2}) :=
    hUo.isOpen_inter_preimage_of_deriv_eq_zero
      (fun s hs => (hder s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hder s hs).deriv) {r ^ 2}
  have heq : γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ = r} = U ∩ G ⁻¹' {r ^ 2} := by
    ext s
    constructor
    · rintro ⟨hys, hyr⟩
      refine ⟨⟨hys, ?_, ?_⟩, ?_⟩
      · change 3 * r / 4 < ‖c (γ s)‖
        rw [hyr]; linarith
      · change ‖c (γ s)‖ < 5 * r / 4
        rw [hyr]; linarith
      · change ‖c (γ s)‖ ^ 2 = r ^ 2
        rw [hyr]
    · rintro ⟨hs, he⟩
      refine ⟨hs.1, ?_⟩
      exact (sq_eq_sq₀ (norm_nonneg _) hr.le).mp he
  have hclosed : IsClosed (γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ = r}) :=
    (chart_sphere_compact c r hball).isClosed.preimage hγcont
  have hopen : IsOpen (γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ = r}) := heq ▸ hVo'
  have hcl : IsClopen (γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ = r}) := ⟨hclosed, hopen⟩
  have hall := hcl.eq_univ ⟨0, by simpa [γ] using hx⟩
  have ht : t ∈ γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ = r} := by rw [hall]; trivial
  exact ht


private theorem chart_closed_ball_flow_invariant
    {E : Type} [TopologicalSpace E] [T2Space E]
    (c : OpenPartialHomeomorph E ℂ) (r : ℝ)
    (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target)
    (φ : Flow ℝ E)
    (hsphere : IsInvariant φ {x : E | x ∈ c.source ∧ ‖c x‖ = r}) :
    IsInvariant φ (actualCriticalChartRegion c r) := by
  intro t x hx
  by_cases heq : ‖c x‖ = r
  · have hy := hsphere t ⟨hx.1, heq⟩
    exact ⟨hy.1, hy.2.le⟩
  let γ : ℝ → E := fun s => φ s x
  have hγcont : Continuous γ := φ.continuous continuous_id continuous_const
  have hnot (s : ℝ) : γ s ∉ {y : E | y ∈ c.source ∧ ‖c y‖ = r} := by
    intro hy
    have hh := hsphere (-s) hy
    have hr : φ (-s) (γ s) = x := by simp [γ, ← φ.map_add]
    rw [hr] at hh
    exact heq hh.2
  have hop : IsOpen {y : E | y ∈ c.source ∧ ‖c y‖ < r} :=
    c.isOpen_inter_preimage (isOpen_lt continuous_norm continuous_const)
  have he : γ ⁻¹' actualCriticalChartRegion c r =
      γ ⁻¹' {y : E | y ∈ c.source ∧ ‖c y‖ < r} := by
    ext s
    constructor
    · intro hs
      exact ⟨hs.1, lt_of_le_of_ne hs.2 (fun heq => hnot s ⟨hs.1, heq⟩)⟩
    · intro hs
      exact ⟨hs.1, hs.2.le⟩
  have hclosed : IsClosed (γ ⁻¹' actualCriticalChartRegion c r) :=
    (actual_partial_chart_closed_ball_region_compact c r hball).isClosed.preimage hγcont
  have hopen : IsOpen (γ ⁻¹' actualCriticalChartRegion c r) := he ▸ hop.preimage hγcont
  have hcl : IsClopen (γ ⁻¹' actualCriticalChartRegion c r) := ⟨hclosed, hopen⟩
  have hall := hcl.eq_univ ⟨0, by simpa [γ] using hx⟩
  have ht : t ∈ γ ⁻¹' actualCriticalChartRegion c r := by rw [hall]; trivial
  exact ht

private theorem flow_height_monotone
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) X)
    (hnon : ∀ x, 0 ≤ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) (x : E) :
    Monotone (fun t => F (φ t x)) := by
  have hd (t : ℝ) := actual_integral_curve_scalar_height_derivative F hF X
    (fun s => φ s x) t ((hcurve x).isMIntegralCurveAt t)
  apply monotone_of_deriv_nonneg
  · exact fun t => (hd t).differentiableAt
  · intro t
    change 0 ≤ deriv (F ∘ fun s => φ s x) t
    rw [(hd t).deriv]
    exact hnon _


private theorem normalize_nonnegative_on_compact
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (K : Set E) (hK : IsCompact K)
    (hpos : ∀ x ∈ K, 0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))) :
    ∃ a : E → ℝ,
      (ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (a x • X x))) ∧
      (∀ x, 0 ≤ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (a x • X x))) ∧
      ∀ x ∈ K, (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (a x • X x)) = 1 := by
  let g : E → ℝ := fun x => (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
    ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x))
  have hgs := actual_smooth_scalar_tangent_field_energy_smooth F hF X hX
  let U : Set E := {x | 0 < g x}
  have hU : IsOpen U := isOpen_lt continuous_const hgs.continuous
  obtain ⟨b, hb, hs, hbounds, hone⟩ := compact_manifold_plateau K U hK hU hpos
  let a : E → ℝ := fun x => b x / g x
  have ha : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ a :=
    actual_smooth_supported_division_by_energy b g hb hgs (fun x hx => ne_of_gt (hs hx))
  have heq (x : E) : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
      ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (a x • X x)) = b x := by
    simp only [map_smul, smul_eq_mul]
    change b x / g x * g x = b x
    by_cases hgx : g x = 0
    · have hbx : b x = 0 := by
        by_contra hbx
        have hp := hs (subset_tsupport b hbx)
        change 0 < g x at hp
        rw [hgx] at hp
        exact (lt_irrefl _ hp)
      simp [hbx]
    · exact div_mul_cancel₀ _ hgx
  exact ⟨a, ha.smul_section hX, fun x => by rw [heq]; exact (hbounds x).1,
    fun x hx => by rw [heq, hone x hx]⟩

private theorem exists_critical_window_adapted_field
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (S : Finset E) (v η : ℝ) (hη : 0 < η)
    (hvalue : ∀ q ∈ S, F q = v)
    (hup : ∀ x, F x ∈ Icc (v - η) (v + η) → x ∉ S →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)))
    (k : E → Fin 3) (c : E → OpenPartialHomeomorph E ℂ)
    (hcenter : ∀ q ∈ S, q ∈ (c q).source ∧ c q q = 0)
    (hchart : ∀ q ∈ S, ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hnormal : ∀ q ∈ S, ∀ x ∈ (c q).source,
      F x = F q + actualCriticalWindowQuadratic (k q) (c q x)) :
    ∃ (ε : ℝ) (ρ : E → ℝ) (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x),
      0 < ε ∧ 2 * ε < η ∧
      (∀ q ∈ S, 0 < ρ q ∧ ε < (ρ q) ^ 2 ∧
        Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target) ∧
      Set.PairwiseDisjoint (↑S : Set E) (fun q => actualCriticalChartRegion (c q) (ρ q)) ∧
      (ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
        (fun x => TotalSpace.mk' ℂ x (Y x))) ∧
      (∀ x, 0 ≤ (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x))) ∧
      (∀ x ∈ actual_critical_chart_complement_band F S c (fun q => ρ q / 2) v (2 * ε),
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
          ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1) ∧
      ∀ q ∈ S, ∀ x, x ∈ (c q).source → 3 * ρ q / 4 < ‖c q x‖ → ‖c q x‖ < 5 * ρ q / 4 →
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (‖c q x‖ ^ 2))
          ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c q y‖ ^ 2) x) (Y x)) = 0 := by
  classical
  obtain ⟨R, hR, hdR⟩ := actual_finite_centered_charts_have_disjoint_compact_balls S c hcenter
  let ρ : E → ℝ := fun q => R q / 2
  have hr (q : E) (hq : q ∈ S) : 0 < ρ q := by dsimp [ρ]; linarith [(hR q hq).1]
  have h2r (q : E) : 2 * ρ q = R q := by dsimp [ρ]; ring
  have hball (q : E) (hq : q ∈ S) : Metric.closedBall (0 : ℂ) (2 * ρ q) ⊆ (c q).target := by
    rw [h2r]; exact (hR q hq).2.1
  have hd : Set.PairwiseDisjoint (↑S : Set E)
      (fun q => actualCriticalChartRegion (c q) (2 * ρ q)) := by
    simpa only [h2r, actualCriticalChartRegion] using hdR
  obtain ⟨ε, hε, hεη, hερ⟩ := actual_finite_positive_values_have_common_smaller_positive
    S (fun q => (ρ q / 2) ^ 2 / 2) (η / 2) (by positivity)
    (fun q hq => by have h := hr q hq; positivity)
  have hbex (q : E) : ∃ b : E → ℝ, q ∈ S →
      ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ b ∧
      (∀ x, 0 ≤ b x ∧ b x ≤ 1) ∧
      tsupport b ⊆ {x | x ∈ (c q).source ∧ ρ q / 2 < ‖c q x‖ ∧ ‖c q x‖ < 2 * ρ q} ∧
      ∀ x, x ∈ (c q).source → 3 * ρ q / 4 ≤ ‖c q x‖ → ‖c q x‖ ≤ 5 * ρ q / 4 → b x = 1 := by
    by_cases hq : q ∈ S
    · obtain ⟨b, hb⟩ := chart_sphere_has_supported_open_collar (c q) (ρ q) (hr q hq) (hball q hq)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨fun _ => 0, fun hp => (hq hp).elim⟩
  choose b hb using hbex
  have hbs := fun q hq => (hb q hq).2.2.1
  let W := collarPatchedField S c b X
  have hW : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (W x)) :=
    collarPatchedField_smooth S c b X hX hchart (fun q hq => (hb q hq).1)
      (fun q hq x hx => (hbs q hq hx).1)
  have hWpos (x : E) (hx : |F x - v| ≤ 2 * ε) (hnot : x ∉ S) :
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (W x)) := by
    apply collarPatchedField_energy_positive S c ρ k b X F v (2 * ε) hchart
      (fun q hq x hx => by rw [hnormal q hq x hx, hvalue q hq])
      (fun q hq => ⟨hr q hq, by linarith [hερ q hq]⟩)
      (fun q hq => (hb q hq).2.1) hbs hd x hx
    apply hup x _ hnot
    have ha := abs_le.mp hx
    constructor <;> linarith
  let K := actual_critical_chart_complement_band F S c (fun q => ρ q / 2) v (2 * ε)
  have hK := actual_critical_chart_complement_band_compact F hF.continuous S c
    (fun q => ρ q / 2) v (2 * ε)
  have hpos (x : E) (hx : x ∈ K) :
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (W x)) := by
    apply hWpos x
    · exact abs_le.mpr ⟨by linarith [hx.1.1], by linarith [hx.1.2]⟩
    · intro hs
      exact hx.2 x hs (actual_center_in_interior_of_chart_closed_ball_region (c x) x
        (hcenter x hs).1 (hcenter x hs).2 (ρ x / 2) (by have h := hr x hs; positivity))
  obtain ⟨a, hY, hnon, hunit⟩ := normalize_nonnegative_on_compact F hF W hW K hK hpos
  refine ⟨ε, ρ, fun x => a x • W x, hε, by linarith, ?_, ?_, hY, hnon, hunit, ?_⟩
  · intro q hq
    refine ⟨hr q hq, ?_, (Metric.closedBall_subset_closedBall ?_).trans (hball q hq)⟩
    · have h := hερ q hq
      nlinarith [sq_nonneg (ρ q)]
    · linarith [hr q hq]
  · intro p hp q hq hpq
    apply (hd hp hq hpq).mono
    · intro x hx
      exact ⟨hx.1, hx.2.trans (by linarith [hr p hp])⟩
    · intro x hx
      exact ⟨hx.1, hx.2.trans (by linarith [hr q hq])⟩
  · intro q hq x hxs hlo hhi
    simp only [map_smul, smul_eq_mul]
    have hz := collarPatchedField_collar_radial S c ρ b X hchart hbs hd q hq x hxs
      ((hb q hq).2.2.2 x hxs hlo.le hhi.le)
    change ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) (fun y => ‖c q y‖ ^ 2) x) (W x)) = 0 at hz
    change a x * _ = 0
    rw [hz, mul_zero]


private theorem critical_window_flow_endpoint
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ) (ρ : E → ℝ)
    (hr : ∀ q ∈ S, 0 < ρ q) (v ε : ℝ) (hε : 0 < ε)
    (Y : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (φ : Flow ℝ E) (hcurve : ∀ x, IsMIntegralCurve (fun t => φ t x) Y)
    (hmono : ∀ x, Monotone (fun t => F (φ t x)))
    (hinv : ∀ q ∈ S, IsInvariant φ (actualCriticalChartRegion (c q) (ρ q)))
    (hunit : ∀ x ∈ actual_critical_chart_complement_band F S c (fun q => ρ q / 2) v (2 * ε),
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (Y x)) = 1)
    (x : E) (hx : F x ≤ v + ε) :
    (∃ q ∈ S, φ (- (3 * ε)) x ∈ actualCriticalChartRegion (c q) (ρ q)) ∨
      F (φ (- (3 * ε)) x) ≤ v - 2 * ε := by
  by_cases hlocal : ∃ q ∈ S, x ∈ actualCriticalChartRegion (c q) (ρ q)
  · obtain ⟨q, hq, hxq⟩ := hlocal
    exact Or.inl ⟨q, hq, hinv q hq _ hxq⟩
  right
  by_contra hhigh
  have hh : v - 2 * ε < F (φ (- (3 * ε)) x) := lt_of_not_ge hhigh
  let K := actual_critical_chart_complement_band F S c (fun q => ρ q / 2) v (2 * ε)
  have havoid (s : ℝ) (q : E) (hq : q ∈ S) :
      φ s x ∉ actualCriticalChartRegion (c q) (ρ q) := by
    intro hy
    have hz := hinv q hq (-s) hy
    have he : φ (-s) (φ s x) = x := by simp [← φ.map_add]
    rw [he] at hz
    exact hlocal ⟨q, hq, hz⟩
  have hinside (s : ℝ) (hs : s ∈ Icc (-(3 * ε)) 0) : φ s x ∈ K := by
    have hlo := hmono x hs.1
    have hhi := hmono x hs.2
    dsimp only at hlo hhi
    rw [φ.map_zero_apply] at hhi
    refine ⟨⟨by linarith, by linarith⟩, ?_⟩
    intro q hq hc
    have hm := interior_subset hc
    apply havoid s q hq
    exact ⟨hm.1, hm.2.trans (by linarith [hr q hq])⟩
  have hheight := actual_normalized_integral_curve_height_translation F hF Y K hunit
    (fun s => φ s x) (-(3 * ε)) 0 (by linarith)
    (fun s _ => (hcurve x).isMIntegralCurveAt s) hinside
  rw [φ.map_zero_apply] at hheight
  linarith


open Set CategoryTheory Topology
open CurveComplexGenusTwo.CWHurewicz

set_option backward.isDefEq.respectTransparency false

private def subsetInclusion {X : Type} [TopologicalSpace X] (B : Set X) : C(B, X) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem pairInclusion_iso_of_homotopy_into
    {X : Type} [TopologicalSpace X] (A C : Set X)
    (g : C(X, X)) (hg : ∀ x, g x ∈ C)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) g)
    (hA : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A)
    (hC : ∀ (t : unitInterval) (x : X), x ∈ C → H (t, x) ∈ C)
    (n : ℕ) :
    IsIso (pairRelativeHomologyMap {x : C | x.1 ∈ A} A (subsetInclusion C)
      (fun _ hx => hx) n) := by
  let AC : Set C := {x | x.1 ∈ A}
  let i := subsetInclusion C
  let r : C(X, C) := ⟨fun x => ⟨g x, hg x⟩, g.continuous.subtype_mk _⟩
  have hr : ∀ x ∈ A, r x ∈ AC := by
    intro x hx
    have h := hA 1 x hx
    simpa [r, AC] using h
  have hi : ∀ x ∈ AC, i x ∈ A := fun _ hx => hx
  let Hc : ContinuousMap.Homotopy (ContinuousMap.id C) (r.comp i) := {
    toFun := fun p => ⟨H (p.1, p.2.1), hC p.1 p.2.1 p.2.2⟩
    continuous_toFun := (H.continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).subtype_mk _
    map_zero_left := by intro x; apply Subtype.ext; exact H.map_zero_left x.1
    map_one_left := by intro x; apply Subtype.ext; exact H.map_one_left x.1
  }
  have HcA : ∀ (t : unitInterval) (x : C), x ∈ AC → Hc (t, x) ∈ AC := by
    intro t x hx
    exact hA t x.1 hx
  let f := pairRelativeHomologyMap AC A i hi n
  let j := pairRelativeHomologyMap A AC r hr n
  have hfj : f ≫ j = 𝟙 _ := by
    dsimp [f, j]
    rw [← pairRelativeHomologyMap_comp]
    rw [← pairRelativeHomologyMap_homotopy AC AC (ContinuousMap.id C) (r.comp i)
      (fun _ hx => hx) (fun x hx => hr (i x) (hi x hx)) Hc HcA n]
    exact pairRelativeHomologyMap_id AC n
  have hji : j ≫ f = 𝟙 _ := by
    dsimp [f, j]
    rw [← pairRelativeHomologyMap_comp]
    change pairRelativeHomologyMap A A g (fun x hx => hi (r x) (hr x hx)) n = _
    rw [← pairRelativeHomologyMap_homotopy A A (ContinuousMap.id X) g
      (fun _ hx => hx) (fun x hx => hi (r x) (hr x hx)) H hA n]
    exact pairRelativeHomologyMap_id A n
  exact ⟨j, hfj, hji⟩

private def unionExcisionHomeomorph
    {X : Type} [TopologicalSpace X] (B D : Set X) :
    B ≃ₜ Excised (B ∪ D : Set X) {x : (B ∪ D : Set X) | x.1 ∉ B} where
  toFun x := ⟨⟨x.1, Or.inl x.2⟩, by simpa using x.2⟩
  invFun x := ⟨x.1.1, by exact Classical.not_not.mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl
  continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private theorem union_complement_closure_in_lower
    {X : Type} [TopologicalSpace X] (A B D : Set X)
    (hD : IsClosed D) (hDA : D ⊆ interior A) :
    closure {x : (B ∪ D : Set X) | x.1 ∉ B} ⊆
      interior {x : (B ∪ D : Set X) | x.1 ∈ A} := by
  have hc : closure {x : (B ∪ D : Set X) | x.1 ∉ B} ⊆ {x : (B ∪ D : Set X) | x.1 ∈ D} :=
    closure_minimal (fun x hx => x.2.resolve_left hx)
      (hD.preimage continuous_subtype_val)
  have hi : {x : (B ∪ D : Set X) | x.1 ∈ interior A} ⊆
      interior {x : (B ∪ D : Set X) | x.1 ∈ A} :=
    interior_maximal (fun x hx => @interior_subset X _ A x.1 hx)
      (isOpen_interior.preimage continuous_subtype_val)
  exact fun x hx => hi (hDA (hc hx))

private theorem pairInclusion_into_union_isIso
    {X : Type} [TopologicalSpace X] (A B D : Set X)
    (hD : IsClosed D) (hDA : D ⊆ interior A) (n : ℕ) :
    IsIso (pairRelativeHomologyMap {x : B | x.1 ∈ A}
      {x : (B ∪ D : Set X) | x.1 ∈ A}
      ⟨fun x => ⟨x.1, Or.inl x.2⟩, continuous_subtype_val.subtype_mk _⟩
      (fun _ hx => hx) n) := by
  let C : Set X := B ∪ D
  let AC : Set C := {x | x.1 ∈ A}
  let U : Set C := {x | x.1 ∉ B}
  let AB : Set B := {x | x.1 ∈ A}
  let e := unionExcisionHomeomorph B D
  let f : C(B, Excised C U) := ⟨e, e.continuous⟩
  let i : C(Excised C U, C) := ⟨Subtype.val, continuous_subtype_val⟩
  have hf : ∀ x ∈ AB, f x ∈ excisedSubspace AC U := fun _ hx => hx
  have hi : ∀ x ∈ excisedSubspace AC U, i x ∈ AC := fun _ hx => hx
  have hfiso : IsIso (pairRelativeHomologyMap AB (excisedSubspace AC U) f hf n) := by
    apply actual_pairRelativeHomologyMap_homeomorph_isIso B (Excised C U) AB
      (excisedSubspace AC U) e
    intro x
    rfl
  have hiso : IsIso (pairRelativeHomologyMap (excisedSubspace AC U) AC i hi n) := by
    have heq : pairRelativeChainMap (excisedSubspace AC U) AC i hi =
        excisionRelativeChainMap AC U := rfl
    unfold pairRelativeHomologyMap
    rw [heq]
    exact actual_canonicalExcisionHomologyMap_isIso C AC U
      (union_complement_closure_in_lower A B D hD hDA) n
  have heq := pairRelativeHomologyMap_comp AB (excisedSubspace AC U) AC f i hf hi n
  change IsIso (pairRelativeHomologyMap AB AC (i.comp f) (fun x hx => hi (f x) (hf x hx)) n)
  rw [heq]
  let _ := hfiso
  let _ := hiso
  infer_instance

private theorem pairInclusion_localizes_of_homotopy
    {X : Type} [TopologicalSpace X] (A B D : Set X)
    (hD : IsClosed D) (hDA : D ⊆ interior A)
    (g : C(X, X)) (hg : ∀ x, g x ∈ B ∪ D)
    (H : ContinuousMap.Homotopy (ContinuousMap.id X) g)
    (hA : ∀ (t : unitInterval) (x : X), x ∈ A → H (t, x) ∈ A)
    (hC : ∀ (t : unitInterval) (x : X), x ∈ B ∪ D → H (t, x) ∈ B ∪ D)
    (n : ℕ) :
    IsIso (pairRelativeHomologyMap {x : B | x.1 ∈ A} A (subsetInclusion B)
      (fun _ hx => hx) n) := by
  let AB : Set B := {x | x.1 ∈ A}
  let AC : Set (B ∪ D : Set X) := {x | x.1 ∈ A}
  let f : C(B, (B ∪ D : Set X)) :=
    ⟨fun x => ⟨x.1, Or.inl x.2⟩, continuous_subtype_val.subtype_mk _⟩
  let i := subsetInclusion (B ∪ D)
  have hf : ∀ x ∈ AB, f x ∈ AC := fun _ hx => hx
  have hi : ∀ x ∈ AC, i x ∈ A := fun _ hx => hx
  have hfiso := pairInclusion_into_union_isIso A B D hD hDA n
  have hiiso := pairInclusion_iso_of_homotopy_into A (B ∪ D) g hg H hA hC n
  have heq := pairRelativeHomologyMap_comp AB AC A f i hf hi n
  change pairRelativeHomologyMap AB A (subsetInclusion B) (fun _ hx => hx) n = _ at heq
  change IsIso (pairRelativeHomologyMap AB A (subsetInclusion B) (fun _ hx => hx) n)
  rw [heq]
  let _ := hfiso
  let _ := hiiso
  infer_instance


/-- Small disjoint literal Morse chart pieces compare to the FULL sublevel
pair through their actual inclusion in EVERY degree, including degree zero.
The supplied real charts are outputs of the separately owned smooth Morse
lemma. The installed charted-space datum is retained. No normal-form or
relative-profile certificate is added to the original sign/Euler theorem. -/
theorem actual_simultaneous_critical_window_inclusion_relativeHomology_isIso
    {E : Type} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (F : E → ℝ) (hF : ContMDiff 𝓘(ℝ,ℂ) 𝓘(ℝ) ∞ F)
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (S : Finset E) (v η : ℝ) (hη : 0 < η)
    (hvalue : ∀ q ∈ S, F q = v)
    (hup : ∀ x : E, F x ∈ Icc (v - η) (v + η) → x ∉ S →
      0 < (NormedSpace.fromTangentSpace (𝕜 := ℝ) (F x))
        ((mfderiv 𝓘(ℝ,ℂ) 𝓘(ℝ) F x) (X x)))
    (k : E → Fin 3) (c : E → OpenPartialHomeomorph E ℂ)
    (hcenter : ∀ q ∈ S, q ∈ (c q).source ∧ c q q = 0)
    (hchart : ∀ q ∈ S,
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q) (c q).source ∧
      ContMDiffOn 𝓘(ℝ,ℂ) 𝓘(ℝ,ℂ) ∞ (c q).symm (c q).target)
    (hnormal : ∀ q ∈ S, ∀ x ∈ (c q).source,
      F x = F q + actualCriticalWindowQuadratic (k q) (c q x)) :
    ∃ (ε : ℝ) (ρ : E → ℝ),
      0 < ε ∧ ε < η ∧
      (∀ q ∈ S, 0 < ρ q ∧ ε < (ρ q) ^ 2 ∧
        Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target) ∧
      Set.PairwiseDisjoint (↑S : Set E)
        (fun q => actualCriticalChartRegion (c q) (ρ q)) ∧
      ∀ n : ℕ,
        IsIso (pairRelativeHomologyMap
          (actualCriticalWindowLocalLower F S c ρ v ε)
          (actualCriticalWindowFullLower F v ε)
          (actualCriticalWindowInclusion F S c ρ v ε)
          (fun _ hx => hx) n) := by
  classical
  obtain ⟨ε, ρ, Y, hε, hεη, hρ, hd, hY, hnon, hunit, hrad⟩ :=
    exists_critical_window_adapted_field F hF X hX S v η hη hvalue hup
      k c hcenter hchart hnormal
  obtain ⟨φ, hcurve⟩ := actual_smooth_complex_field_has_global_flow Y hY
  have hmono := flow_height_monotone F hF Y φ hcurve hnon
  have hinv (q : E) (hq : q ∈ S) :
      IsInvariant φ (actualCriticalChartRegion (c q) (ρ q)) :=
    chart_closed_ball_flow_invariant (c q) (ρ q) (hρ q hq).2.2 φ
      (chart_sphere_flow_invariant (c q) (hchart q hq).1 (ρ q) (hρ q hq).1
        (hρ q hq).2.2 Y φ hcurve (hrad q hq))
  have hdecrease (u : unitInterval) (x : E) :
      F (φ (-((u : ℝ) * (3 * ε))) x) ≤ F x := by
    have hh := hmono x (show -((u : ℝ) * (3 * ε)) ≤ 0 from by
      exact neg_nonpos.mpr (mul_nonneg u.2.1 (by linarith)))
    simpa using hh
  refine ⟨ε, ρ, hε, by linarith, hρ, hd, ?_⟩
  intro n
  let M := {x : E // F x ≤ v + ε}
  let A : Set M := {x | F x.1 ≤ v - ε}
  let B : Set M := {x | ∃ q ∈ S, x.1 ∈ actualCriticalChartRegion (c q) (ρ q)}
  let D : Set M := {x | F x.1 ≤ v - 2 * ε}
  have hgend (x : M) : F (φ (-(3 * ε)) x.1) ≤ v + ε := by
    have hh : F (φ (-(3 * ε)) x.1) ≤ F x.1 := by simpa using hdecrease 1 x.1
    exact hh.trans x.2
  let g : C(M, M) :=
    ⟨fun x => ⟨φ (-(3 * ε)) x.1, hgend x⟩,
      (φ.continuous continuous_const continuous_subtype_val).subtype_mk hgend⟩
  let H : ContinuousMap.Homotopy (ContinuousMap.id M) g := {
    toFun := fun p => ⟨φ (-((p.1 : ℝ) * (3 * ε))) p.2.1,
      (hdecrease p.1 p.2.1).trans p.2.2⟩
    continuous_toFun := (φ.continuous
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).neg)
      (continuous_subtype_val.comp continuous_snd)).subtype_mk _
    map_zero_left := by intro x; apply Subtype.ext; simp
    map_one_left := by intro x; apply Subtype.ext; simp [g]
  }
  have hA : ∀ (u : unitInterval) (x : M), x ∈ A → H (u, x) ∈ A :=
    fun u x hx => (hdecrease u x.1).trans hx
  have hC : ∀ (u : unitInterval) (x : M), x ∈ B ∪ D → H (u, x) ∈ B ∪ D := by
    intro u x hx
    rcases hx with ⟨q, hq, hxq⟩ | hx
    · exact Or.inl ⟨q, hq, hinv q hq _ hxq⟩
    · exact Or.inr ((hdecrease u x.1).trans hx)
  have hg : ∀ x : M, g x ∈ B ∪ D := by
    intro x
    exact critical_window_flow_endpoint F hF S c ρ (fun q hq => (hρ q hq).1)
      v ε hε Y φ hcurve hmono hinv hunit x.1 x.2
  have hD : IsClosed D := isClosed_le (hF.continuous.comp continuous_subtype_val) continuous_const
  have hDA : D ⊆ interior A := by
    have hi : {x : M | F x.1 < v - ε} ⊆ interior A :=
      interior_maximal (fun x hx => (show F x.1 ≤ v - ε from hx.le))
        (isOpen_lt (hF.continuous.comp continuous_subtype_val) continuous_const)
    intro x hx
    apply hi
    change F x.1 ≤ v - 2 * ε at hx
    change F x.1 < v - ε
    linarith
  have hBi := pairInclusion_localizes_of_homotopy A B D hD hDA g hg H hA hC n
  let e : actualCriticalWindowLocalUpper F S c ρ v ε ≃ₜ B := {
    toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
    invFun := fun x => ⟨x.1.1, x.2, x.1.2⟩
    left_inv := by intro x; apply Subtype.ext; rfl
    right_inv := by intro x; apply Subtype.ext; apply Subtype.ext; rfl
    continuous_toFun := (continuous_subtype_val.subtype_mk _).subtype_mk _
    continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  }
  let AL := actualCriticalWindowLocalLower F S c ρ v ε
  let AB : Set B := {x | x.1 ∈ A}
  let f : C(actualCriticalWindowLocalUpper F S c ρ v ε, B) := ⟨e, e.continuous⟩
  let i := subsetInclusion B
  have hf : ∀ x ∈ AL, f x ∈ AB := fun _ hx => hx
  have hi : ∀ x ∈ AB, i x ∈ A := fun _ hx => hx
  have hfi : IsIso (pairRelativeHomologyMap AL AB f hf n) := by
    apply actual_pairRelativeHomologyMap_homeomorph_isIso _ _ AL AB e
    intro x
    rfl
  have heq := pairRelativeHomologyMap_comp AL AB A f i hf hi n
  change IsIso (pairRelativeHomologyMap AL A (i.comp f) (fun x hx => hi (f x) (hf x hx)) n)
  rw [heq]
  let _ := hfi
  let _ := hBi
  infer_instance

#print axioms actual_simultaneous_critical_window_inclusion_relativeHomology_isIso
