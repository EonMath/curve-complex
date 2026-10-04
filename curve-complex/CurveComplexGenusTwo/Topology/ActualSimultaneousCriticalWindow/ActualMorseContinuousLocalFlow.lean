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
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseChartIntegralCurve

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function Metric Filter

set_option backward.isDefEq.respectTransparency false in
theorem actual_smooth_complex_field_has_continuous_local_flow
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x))) (p : E) :
    ∃ (U : Set E) (ε : ℝ) (Φ : E × ℝ → E),
      IsOpen U ∧ p ∈ U ∧ 0 < ε ∧
      ContinuousOn Φ (U ×ˢ Ioo (-ε) ε) ∧
      ∀ x ∈ U, Φ (x, 0) = x ∧
        IsMIntegralCurveOn (fun t => Φ (x, t)) X (Ioo (-ε) ε) := by
  have hv := (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞)).contMDiffAt (x := p)
  rw [contMDiffAt_iff] at hv
  obtain ⟨_, hv⟩ := hv
  have hf := (hv.contDiffAt (by simp)).snd
  obtain ⟨ε₀, hε₀, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one hf
  obtain ⟨α, hα, hcont⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_continuousOn
  simp only [zero_sub, zero_add] at hα hcont
  let c := extChartAt 𝓘(ℝ,ℂ) p
  have hcenter : α (c p, 0) = c p :=
    (hα (c p) (mem_closedBall_self hr.le)).1
  have hdomain : closedBall (c p) (r : ℝ) ×ˢ Icc (-ε₀) ε₀ ∈ 𝓝 (c p, 0) := by
    exact prod_mem_nhds (closedBall_mem_nhds _ hr)
      (Icc_mem_nhds (by linarith) (by linarith))
  have hcontAt : ContinuousAt α (c p, 0) := by
    apply hcont.continuousAt
    simpa [c] using hdomain
  have himage : α ⁻¹' c.target ∈ 𝓝 (c p, 0) := by
    apply hcontAt.preimage_mem_nhds
    rw [hcenter]
    exact extChartAt_target_mem_nhds (I := 𝓘(ℝ,ℂ)) p
  obtain ⟨S, hS, T, hT, hST⟩ := mem_nhds_prod_iff.mp (inter_mem hdomain himage)
  obtain ⟨d, hd, hball⟩ := Metric.mem_nhds_iff.mp hS
  obtain ⟨e, he, heT⟩ := Metric.mem_nhds_iff.mp hT
  let U : Set E := c.source ∩ c ⁻¹' ball (c p) d
  let ε : ℝ := min e ε₀
  have hε : 0 < ε := lt_min he hε₀
  have hU : IsOpen U := by
    exact (continuousOn_extChartAt (I := 𝓘(ℝ,ℂ)) p).isOpen_inter_preimage
      (by simpa [c] using (chartAt ℂ p).open_source) isOpen_ball
  have hpU : p ∈ U := ⟨mem_extChartAt_source p, mem_ball_self hd⟩
  have hrectangle : ∀ x ∈ U, ∀ t ∈ Ioo (-ε) ε,
      (c x, t) ∈ closedBall (c p) (r : ℝ) ×ˢ Icc (-ε₀) ε₀ ∧
        α (c x, t) ∈ c.target := by
    intro x hx t ht
    apply hST
    refine ⟨hball hx.2, heT ?_⟩
    rw [Real.ball_eq_Ioo]
    dsimp [ε] at ht
    constructor <;> linarith [ht.1, ht.2, min_le_left e ε₀]
  let Φ : E × ℝ → E := fun q => c.symm (α (c q.1, q.2))
  refine ⟨U, ε, Φ, hU, hpU, hε, ?_, ?_⟩
  · have hc : ContinuousOn (fun q : E × ℝ => (c q.1, q.2))
        (U ×ˢ Ioo (-ε) ε) := by
      exact ((continuousOn_extChartAt (I := 𝓘(ℝ,ℂ)) p).comp continuousOn_fst
        (fun q hq => hq.1.1)).prodMk continuousOn_snd
    exact (continuousOn_extChartAt_symm (I := 𝓘(ℝ,ℂ)) p).comp (hcont.comp hc
      (fun q hq => (hrectangle q.1 hq.1 q.2 hq.2).1))
      (fun q hq => (hrectangle q.1 hq.1 q.2 hq.2).2)
  · intro x hx
    have hzero : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
    have hxball := (hrectangle x hx 0 hzero).1.1
    refine ⟨?_, ?_⟩
    · dsimp [Φ]
      rw [(hα (c x) hxball).1]
      exact c.left_inv hx.1
    · apply actual_chart_solution_is_integral_curve_on X p
        (fun t => α (c x, t)) (Ioo (-ε) ε) isOpen_Ioo
      · intro t ht
        have hinterval := (hrectangle x hx t ht).1.2
        have hstrict : t ∈ Ioo (-ε₀) ε₀ := by
          dsimp [ε] at ht
          constructor <;> linarith [ht.1, ht.2, min_le_right e ε₀]
        exact ((hα (c x) hxball).2 t hinterval).hasDerivAt
          (Icc_mem_nhds hstrict.1 hstrict.2)
      · exact fun t ht => (hrectangle x hx t ht).2

#print axioms actual_smooth_complex_field_has_continuous_local_flow
