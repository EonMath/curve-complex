import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnQuarterMetric

namespace CurveComplex.Hyperbolic
open Set Topology

theorem vertexHalfTurn_fixed_iff (z : H2) : vertexHalfTurnEquiv z = z ↔ z.re = 0 ∧ z.im = 1 := by
  constructor
  · intro hz
    have hr := congrArg UpperHalfPlane.re hz
    have hi := congrArg UpperHalfPlane.im hz
    change (verticalReflectionEquiv (unitCircleReflectionEquiv z)).re = z.re at hr
    change (verticalReflectionEquiv (unitCircleReflectionEquiv z)).im = z.im at hi
    rw [verticalReflection_re, unitCircleReflection_re] at hr
    rw [verticalReflection_im, unitCircleReflection_im] at hi
    have hn : z.re ^ 2 + z.im ^ 2 > 0 := by nlinarith [z.im_pos]
    rw [div_eq_iff (ne_of_gt hn)] at hi
    have hnorm : z.re ^ 2 + z.im ^ 2 = 1 := by nlinarith [z.im_pos]
    rw [hnorm, div_one] at hr
    have hre : z.re = 0 := by linarith
    refine ⟨hre, ?_⟩
    rw [hre] at hnorm
    nlinarith [z.im_pos]
  · rintro ⟨hr, hi⟩
    exact vertexHalfTurn_fixes_normalized_vertex z hr hi

theorem halfTurnMetricCone_eq_iff (a b : H2) :
    toHalfTurnMetricCone a = toHalfTurnMetricCone b ↔ a = b ∨ a = vertexHalfTurnEquiv b := by
  rw [← dist_eq_zero, halfTurnMetricCone_distance]
  constructor
  · intro hz
    rcases le_total (dist a b) (dist a (vertexHalfTurnEquiv b)) with h | h
    · rw [min_eq_left h] at hz
      exact Or.inl (dist_eq_zero.mp hz)
    · rw [min_eq_right h] at hz
      exact Or.inr (dist_eq_zero.mp hz)
  · rintro (rfl | rfl)
    · rw [dist_self]; exact min_eq_left dist_nonneg
    · rw [dist_self]; exact min_eq_right dist_nonneg

theorem halfTurnMetricCone_isometry_on_small_ball (z : H2)
    (hz : vertexHalfTurnEquiv z ≠ z) :
    Isometry (fun a : Metric.ball z (dist z (vertexHalfTurnEquiv z) / 4) =>
      toHalfTurnMetricCone a.val) := by
  apply Isometry.of_dist_eq
  intro a b
  rw [halfTurnMetricCone_distance]
  change min (dist a.val b.val) (dist a.val (vertexHalfTurnEquiv b.val)) = dist a.val b.val
  apply min_eq_left
  have ha : dist a.val z < dist z (vertexHalfTurnEquiv z) / 4 := a.property
  have hb : dist b.val z < dist z (vertexHalfTurnEquiv z) / 4 := b.property
  have ht := dist_triangle a.val z b.val
  have hs := dist_triangle z a.val (vertexHalfTurnEquiv z)
  have hs' := dist_triangle a.val (vertexHalfTurnEquiv b.val) (vertexHalfTurnEquiv z)
  rw [vertexHalfTurnEquiv.dist_eq] at hs'
  rw [dist_comm z a.val] at hs
  rw [dist_comm z b.val] at ht
  linarith

theorem halfTurnMetricCone_small_ball_image (z : H2) :
    toHalfTurnMetricCone '' Metric.ball z (dist z (vertexHalfTurnEquiv z) / 4) =
      Metric.ball (toHalfTurnMetricCone z) (dist z (vertexHalfTurnEquiv z) / 4) := by
  ext w
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact lt_of_le_of_lt (halfTurnMetricCone_projection_distance_le a z) ha
  · intro hw
    obtain ⟨⟨a⟩, rfl⟩ := SeparationQuotient.surjective_mk w
    change dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone z) < _ at hw
    rw [halfTurnMetricCone_distance, min_lt_iff] at hw
    rcases hw with ha | ha
    · exact ⟨a, ha, rfl⟩
    · refine ⟨vertexHalfTurnEquiv a, ?_, halfTurnMetricCone_halfTurn_eq a⟩
      change dist (vertexHalfTurnEquiv a) z < _
      calc
        dist (vertexHalfTurnEquiv a) z = dist (vertexHalfTurnEquiv a)
            (vertexHalfTurnEquiv (vertexHalfTurnEquiv z)) :=
          congrArg (dist (vertexHalfTurnEquiv a)) (vertexHalfTurn_involutive z).symm
        _ = dist a (vertexHalfTurnEquiv z) := vertexHalfTurnEquiv.dist_eq _ _
        _ < _ := ha

end CurveComplex.Hyperbolic
