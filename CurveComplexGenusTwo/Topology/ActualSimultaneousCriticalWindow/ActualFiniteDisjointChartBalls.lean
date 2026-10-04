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

open Set Topology

theorem actual_partial_chart_closed_ball_region_eq_image
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (r : ℝ) (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target) :
    {x : E | x ∈ c.source ∧ ‖c x‖ ≤ r} =
      c.symm '' Metric.closedBall (0 : ℂ) r := by
  ext x
  constructor
  · intro hx
    exact ⟨c x, by simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2,
      c.left_inv hx.1⟩
  · rintro ⟨z, hz, rfl⟩
    have hzt := hball hz
    refine ⟨c.symm.map_source hzt, ?_⟩
    rw [c.right_inv hzt]
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz

theorem actual_partial_chart_closed_ball_region_compact
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (r : ℝ) (hball : Metric.closedBall (0 : ℂ) r ⊆ c.target) :
    IsCompact {x : E | x ∈ c.source ∧ ‖c x‖ ≤ r} := by
  rw [actual_partial_chart_closed_ball_region_eq_image c r hball]
  exact (isCompact_closedBall (0 : ℂ) r).image_of_continuousOn
    (c.symm.continuousOn.mono hball)

theorem actual_finite_centered_charts_have_disjoint_compact_balls
    {E : Type} [TopologicalSpace E] [T2Space E]
    (S : Finset E) (c : E → OpenPartialHomeomorph E ℂ)
    (hcenter : ∀ q ∈ S, q ∈ (c q).source ∧ c q q = 0) :
    ∃ ρ : E → ℝ,
      (∀ q ∈ S, 0 < ρ q ∧
        Metric.closedBall (0 : ℂ) (ρ q) ⊆ (c q).target ∧
        IsCompact {x : E | x ∈ (c q).source ∧ ‖c q x‖ ≤ ρ q}) ∧
      Set.PairwiseDisjoint (↑S : Set E)
        (fun q => {x : E | x ∈ (c q).source ∧ ‖c q x‖ ≤ ρ q}) := by
  classical
  obtain ⟨U, hU, hdisjoint⟩ := S.finite_toSet.t2_separation
  have hex (q : E) : ∃ r : ℝ, q ∈ S →
      0 < r ∧ Metric.closedBall (0 : ℂ) r ⊆ (c q).target ∧
      {x : E | x ∈ (c q).source ∧ ‖c q x‖ ≤ r} ⊆ U q := by
    by_cases hq : q ∈ S
    · obtain ⟨hqs, hcq⟩ := hcenter q hq
      let V := (c q).target ∩ (c q).symm ⁻¹' U q
      have hVo : IsOpen V := (c q).isOpen_inter_preimage_symm (hU q).2
      have hz : (0 : ℂ) ∈ V := by
        refine ⟨?_, ?_⟩
        · simpa only [hcq] using (c q).map_source hqs
        · change (c q).symm 0 ∈ U q
          rw [← hcq, (c q).left_inv hqs]
          exact (hU q).1
      obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (hVo.mem_nhds hz)
      refine ⟨r, fun _ => ⟨hr, fun z hz => (hball hz).1, ?_⟩⟩
      intro x hx
      have hcx : c q x ∈ V := hball (by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hx.2)
      have hmem : (c q).symm (c q x) ∈ U q := hcx.2
      simpa only [(c q).left_inv hx.1] using hmem
    · exact ⟨1, fun h => False.elim (hq h)⟩
  choose ρ hρ using hex
  refine ⟨ρ, ?_, ?_⟩
  · intro q hq
    obtain ⟨hr, hball, _⟩ := hρ q hq
    exact ⟨hr, hball, actual_partial_chart_closed_ball_region_compact (c q) (ρ q) hball⟩
  · intro p hp q hq hpq
    exact (hdisjoint hp hq hpq).mono (hρ p hp).2.2 (hρ q hq).2.2

theorem actual_finite_positive_values_have_common_smaller_positive
    {I : Type*} (S : Finset I) (w : I → ℝ) (η : ℝ)
    (hη : 0 < η) (hw : ∀ q ∈ S, 0 < w q) :
    ∃ ε : ℝ, 0 < ε ∧ ε < η ∧ ∀ q ∈ S, ε < w q := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨η / 2, by positivity, by linarith, by simp⟩
  | @insert q S hq ih =>
      obtain ⟨ε, hε, hεη, hεw⟩ := ih (fun p hp => hw p (Finset.mem_insert_of_mem hp))
      have hqw : 0 < w q := hw q (Finset.mem_insert_self q S)
      refine ⟨min ε (w q / 2), lt_min hε (by positivity),
        lt_of_le_of_lt (min_le_left _ _) hεη, ?_⟩
      intro p hp
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
      · exact lt_of_le_of_lt (min_le_left _ _) (hεw p hp)

theorem actual_center_in_interior_of_chart_closed_ball_region
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (q : E) (hqs : q ∈ c.source) (hcq : c q = 0)
    (r : ℝ) (hr : 0 < r) :
    q ∈ interior {x : E | x ∈ c.source ∧ ‖c x‖ ≤ r} := by
  have ho := c.isOpen_inter_preimage (Metric.isOpen_ball (x := (0 : ℂ)) (ε := r))
  have hsub : c.source ∩ c ⁻¹' Metric.ball (0 : ℂ) r ⊆
      {x : E | x ∈ c.source ∧ ‖c x‖ ≤ r} := by
    intro x hx
    have hb : c x ∈ Metric.ball (0 : ℂ) r := hx.2
    have hnorm : ‖c x‖ < r := by
      simpa only [Metric.mem_ball, dist_zero_right] using hb
    exact ⟨hx.1, hnorm.le⟩
  apply interior_maximal hsub ho
  exact ⟨hqs, by simpa [hcq] using hr⟩

