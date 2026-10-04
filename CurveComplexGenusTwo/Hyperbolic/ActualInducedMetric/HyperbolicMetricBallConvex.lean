import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
namespace CurveComplex.Hyperbolic
open Set

private theorem vertical_cosh_distance_convex (c : H2) :
    ConvexOn ℝ Set.univ (fun u : ℝ =>
      ((c.re)^2 + (c.im)^2) / (2 * c.im) * Real.exp (-u) +
        (1 / (2 * c.im)) * Real.exp u) := by
  have hn : ConvexOn ℝ Set.univ (fun u : ℝ => Real.exp (-u)) := by
    simpa only [Set.preimage_univ, Function.comp_def, LinearMap.neg_apply, LinearMap.id_apply]
      using convexOn_exp.comp_linearMap (-LinearMap.id (R := ℝ) (M := ℝ))
  exact (hn.smul (by positivity)).add (convexOn_exp.smul (by positivity))

private theorem cosh_distance_on_vertical (c z : H2) (hz : z.re = 0) :
    Real.cosh (dist c z) =
      ((c.re)^2 + (c.im)^2) / (2 * c.im) * Real.exp (-Real.log z.im) +
        (1 / (2 * c.im)) * Real.exp (Real.log z.im) := by
  rw [UpperHalfPlane.cosh_dist', hz, Real.exp_neg, Real.exp_log z.im_pos]
  have hc := c.im_ne_zero
  have hzi := z.im_ne_zero
  field_simp
  ring

theorem metric_segment_cosh_distance_le_max (c a b z : H2)
    (hz : dist a z + dist z b = dist a b) :
    Real.cosh (dist c z) ≤ max (Real.cosh (dist c a)) (Real.cosh (dist c b)) := by
  obtain ⟨e, ha, hb⟩ := exists_pair_vertical_isometry a b
  obtain ⟨hze, hu⟩ := (metric_segment_iff_in_vertical_interval e a b z ha hb).mp hz
  rw [← e.dist_eq c z, ← e.dist_eq c a, ← e.dist_eq c b,
    cosh_distance_on_vertical (e c) (e z) hze,
    cosh_distance_on_vertical (e c) (e a) ha,
    cosh_distance_on_vertical (e c) (e b) hb]
  apply (vertical_cosh_distance_convex (e c)).le_on_segment (Set.mem_univ _) (Set.mem_univ _)
  rwa [segment_eq_uIcc]

theorem metric_segment_stays_in_hyperbolic_ball (c a b z : H2) {r : ℝ}
    (ha : a ∈ Metric.ball c r) (hb : b ∈ Metric.ball c r)
    (hz : dist a z + dist z b = dist a b) : z ∈ Metric.ball c r := by
  have hr : 0 < r := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp ha)
  have h1 := metric_segment_cosh_distance_le_max c a b z hz
  have hca : Real.cosh (dist c a) < Real.cosh r :=
    Real.cosh_strictMonoOn dist_nonneg hr.le (by simpa [Metric.mem_ball, dist_comm] using ha)
  have hcb : Real.cosh (dist c b) < Real.cosh r :=
    Real.cosh_strictMonoOn dist_nonneg hr.le (by simpa [Metric.mem_ball, dist_comm] using hb)
  have hh : Real.cosh (dist c z) < Real.cosh r := lt_of_le_of_lt h1 (max_lt hca hcb)
  apply Metric.mem_ball.mpr
  rw [dist_comm]
  by_contra hn
  have := Real.cosh_strictMonoOn.monotoneOn hr.le dist_nonneg (le_of_not_gt hn)
  exact (not_le_of_gt hh) this
end CurveComplex.Hyperbolic
