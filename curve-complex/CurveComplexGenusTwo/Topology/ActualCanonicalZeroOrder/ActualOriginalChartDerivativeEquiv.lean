import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualCenteredChartTransitionSmooth
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualCenteredChartTransitionInverse
import CurveComplexGenusTwo.Topology.ActualCanonicalZeroOrder.ActualChartInverseDerivativeEquiv

open scoped Manifold ContDiff Topology

theorem actual_original_chart_transition_derivative_equiv
    {E : Type*} [TopologicalSpace E] [ChartedSpace ℂ E]
    [IsManifold 𝓘(ℝ,ℂ) ∞ E]
    (q r : E) (hqr : q ∈ (chartAt ℂ r).source) :
    ∃ H : ℂ ≃L[ℝ] ℂ,
      HasFDerivAt
        (fun w : ℂ =>
          (chartAt ℂ r) ((chartAt ℂ q).symm ((chartAt ℂ q) q + w)) -
            (chartAt ℂ r) q)
        H.toContinuousLinearMap 0 := by
  let h : ℂ → ℂ := fun w =>
    (chartAt ℂ r) ((chartAt ℂ q).symm ((chartAt ℂ q) q + w)) -
      (chartAt ℂ r) q
  let k : ℂ → ℂ := fun w =>
    (chartAt ℂ q) ((chartAt ℂ r).symm ((chartAt ℂ r) q + w)) -
      (chartAt ℂ q) q
  have hh : ContDiffAt ℝ 1 h 0 :=
    actual_centered_chart_transition_contDiffAt q q r (mem_chart_source ℂ q) hqr
  have hk : ContDiffAt ℝ 1 k 0 :=
    actual_centered_chart_transition_contDiffAt q r q hqr (mem_chart_source ℂ q)
  obtain ⟨h0, k0, hkh, hhk⟩ :=
    actual_centered_chart_transition_local_inverse q r hqr
  exact actual_local_inverse_derivative_equiv h k hh hk h0 k0 hkh hhk

#print axioms actual_original_chart_transition_derivative_equiv
