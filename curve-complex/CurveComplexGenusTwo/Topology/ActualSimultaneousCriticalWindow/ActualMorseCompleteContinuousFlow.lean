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
import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualMorseCompleteFlow

open scoped Manifold ContDiff Bundle Topology
open Bundle Set Function Metric Filter

theorem actual_complete_flow_continuous_on_uniform_time
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (Φ : E → ℝ → E) (hzero : ∀ x, Φ x 0 = x)
    (hcurve : ∀ x, IsMIntegralCurve (Φ x) X) :
    ∃ ε : ℝ, 0 < ε ∧ ContinuousOn (uncurry Φ) (univ ×ˢ Ioo (-ε) ε) := by
  classical
  have hlocal := actual_smooth_complex_field_has_continuous_local_flow X hX
  choose U e Ψ hU hp he hcont hlocalcurve using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hp x⟩)
  have hmin : ∃ ε : ℝ, 0 < ε ∧ ∀ p ∈ s, ε ≤ e p := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert p s hps ih =>
      obtain ⟨ε, hε, hbound⟩ := ih
      refine ⟨min ε (e p), lt_min hε (he p), ?_⟩
      intro q hq
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (hbound q hq)
  obtain ⟨ε, hε, hbound⟩ := hmin
  refine ⟨ε, hε, ?_⟩
  intro q hq
  obtain ⟨p, hp, hx⟩ := mem_iUnion₂.mp (hs (mem_univ q.1))
  have hsub : Ioo (-ε) ε ⊆ Ioo (-e p) (e p) :=
    Ioo_subset_Ioo (neg_le_neg (hbound p hp)) (hbound p hp)
  have heq : EqOn (uncurry Φ) (Ψ p) (U p ×ˢ Ioo (-e p) (e p)) := by
    intro z hz
    exact isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless (t₀ := 0)
      ⟨by linarith [he p], he p⟩
      (hX.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ ∞))
      ((hcurve z.1).isMIntegralCurveOn _)
      (hlocalcurve p z.1 hz.1).2
      (by rw [hzero, (hlocalcurve p z.1 hz.1).1]) hz.2
  have hq' : q ∈ U p ×ˢ Ioo (-e p) (e p) := ⟨hx, hsub hq.2⟩
  have hn : U p ×ˢ Ioo (-e p) (e p) ∈ 𝓝 q :=
    ((hU p).prod isOpen_Ioo).mem_nhds hq'
  exact ((hcont p q hq').continuousAt hn).congr
    (Filter.EventuallyEq.symm (Filter.eventually_of_mem hn heq)) |>.continuousWithinAt

#print axioms actual_complete_flow_continuous_on_uniform_time

theorem actual_complete_flow_continuous_at_every_fixed_time
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (Φ : E → ℝ → E) (hzero : ∀ x, Φ x 0 = x)
    (hcurve : ∀ x, IsMIntegralCurve (Φ x) X)
    (hadd : ∀ x s t, Φ x (s + t) = Φ (Φ x s) t) :
    ∀ t, Continuous (fun x => Φ x t) := by
  obtain ⟨ε, hε, hcont⟩ :=
    actual_complete_flow_continuous_on_uniform_time X hX Φ hzero hcurve
  have hsmall : ∀ t, |t| < ε → Continuous (fun x => Φ x t) := by
    intro t ht
    apply continuous_iff_continuousAt.mpr
    intro x
    have hxt : (x, t) ∈ univ ×ˢ Ioo (-ε) ε := ⟨mem_univ x, abs_lt.mp ht⟩
    exact ((hcont (x, t) hxt).continuousAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hxt)).comp
      (f := fun y : E => (y, t))
      (continuousAt_id.prodMk continuousAt_const)
  intro t
  obtain ⟨n, hn⟩ := exists_nat_gt (|t| / ε)
  have hnpos : 0 < (n : ℝ) := lt_of_le_of_lt (by positivity) hn
  let u : ℝ := t / n
  have hu : |u| < ε := by
    dsimp [u]
    rw [abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
    simpa [mul_comm] using (div_lt_iff₀ hε).mp hn
  have hmult : ∀ m : ℕ, Continuous (fun x => Φ x ((m : ℝ) * u)) := by
    intro m
    induction m with
    | zero =>
      have hh : (fun x => Φ x ((0 : ℝ) * u)) = id := by
        funext x
        simp [hzero]
      simpa only [Nat.cast_zero, hh] using (continuous_id : Continuous (id : E → E))
    | succ m ih =>
      have hstep : (fun x => Φ x (((m + 1 : ℕ) : ℝ) * u)) =
          (fun x => Φ (Φ x ((m : ℝ) * u)) u) := by
        funext x
        rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, hadd]
      rw [hstep]
      exact (hsmall u hu).comp ih
  have hnu : (n : ℝ) * u = t := by
    dsimp [u]
    exact mul_div_cancel₀ t (ne_of_gt hnpos)
  simpa only [hnu] using hmult n

#print axioms actual_complete_flow_continuous_at_every_fixed_time

theorem actual_complete_flow_jointly_continuous
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x)))
    (Φ : E → ℝ → E) (hzero : ∀ x, Φ x 0 = x)
    (hcurve : ∀ x, IsMIntegralCurve (Φ x) X)
    (hadd : ∀ x s t, Φ x (s + t) = Φ (Φ x s) t) :
    Continuous (uncurry Φ) := by
  obtain ⟨ε, hε, hcont⟩ :=
    actual_complete_flow_continuous_on_uniform_time X hX Φ hzero hcurve
  have hfixed :=
    actual_complete_flow_continuous_at_every_fixed_time X hX Φ hzero hcurve hadd
  apply continuous_iff_continuousAt.mpr
  rintro ⟨x, t⟩
  have hxt : (Φ x t, 0) ∈ univ ×ˢ Ioo (-ε) ε :=
    ⟨mem_univ _, by constructor <;> linarith⟩
  have hbase : ContinuousAt (uncurry Φ) (Φ x t, 0) :=
    (hcont (Φ x t, 0) hxt).continuousAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds hxt)
  have hinner : ContinuousAt
      (fun q : E × ℝ => (Φ q.1 t, q.2 - t)) (x, t) :=
    ((hfixed t).continuousAt.comp continuousAt_fst).prodMk
      (continuousAt_snd.sub continuousAt_const)
  have hh := hbase.comp_of_eq hinner (by simp)
  have heq : (uncurry Φ ∘ (fun q : E × ℝ => (Φ q.1 t, q.2 - t))) =
      uncurry Φ := by
    funext q
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
    rw [← hadd, add_sub_cancel]
    rfl
  rwa [heq] at hh

#print axioms actual_complete_flow_jointly_continuous

theorem actual_smooth_complex_field_has_global_flow
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E] [CompactSpace E] [T2Space E]
    (X : ∀ x : E, TangentSpace 𝓘(ℝ,ℂ) x)
    (hX : ContMDiff 𝓘(ℝ,ℂ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℂ)) ∞
      (fun x => TotalSpace.mk' ℂ x (X x))) :
    ∃ φ : Flow ℝ E, ∀ x, IsMIntegralCurve (fun t => φ t x) X := by
  obtain ⟨Φ, hzero, hcurve, hadd, _⟩ :=
    actual_smooth_complex_field_complete_flow_laws X hX
  have hcont := actual_complete_flow_jointly_continuous X hX Φ hzero hcurve hadd
  refine ⟨⟨fun t x => Φ x t, ?_, ?_, hzero⟩, hcurve⟩
  · exact hcont.comp continuous_swap
  · intro s t x
    rw [add_comm, hadd]

#print axioms actual_smooth_complex_field_has_global_flow
