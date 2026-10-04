import CurveComplexGenusTwo.Topology.ActualIntervalLocalComparison.ActualOneFormBridge

open scoped Manifold ContDiff Bundle

namespace CanonicalDimensionTwo

theorem actualLocalOneForm_differentiableOn_closedBall
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (c : ℂ) (R : ℝ)
    (htarget : Metric.closedBall c R ⊆ (chartAt ℂ q).target) :
    DifferentiableOn ℂ
      (fun z => actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ)))
      (Metric.closedBall c R) := by
  intro z hz
  have hzt : z ∈ (chartAt ℂ q).target := htarget hz
  have hsrc : (chartAt ℂ q).symm z ∈ (chartAt ℂ q).source :=
    (chartAt ℂ q).map_target hzt
  have ha := actualLocalOneForm_coefficient_analytic_on_chart s q
    ((chartAt ℂ q).symm z) hsrc
  rw [(chartAt ℂ q).right_inv hzt] at ha
  exact ha.differentiableAt.differentiableWithinAt

theorem actualLocalOneForm_circleIntegral_cauchy
    {E : Type*} [TopologicalSpace E]
    [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (q : E) (c : ℂ) (R : ℝ)
    (hR : 0 < R)
    (htarget : Metric.closedBall c R ⊆ (chartAt ℂ q).target) :
    (∮ z in C(c, R), (z - c)⁻¹ •
      actualLocalOneForm s q z (fun _ : Fin 1 => (1 : ℂ))) =
      (2 * Real.pi * Complex.I) •
        actualLocalOneForm s q c (fun _ : Fin 1 => (1 : ℂ)) := by
  have hd := actualLocalOneForm_differentiableOn_closedBall s q c R htarget
  simpa only [one_div, zero_add, pow_one, Nat.factorial_zero, Nat.cast_one, div_one,
    iteratedDeriv_zero] using
    (hd.circleIntegral_one_div_sub_center_pow_smul hR 0)

end CanonicalDimensionTwo
