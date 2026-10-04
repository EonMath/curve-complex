import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactHalfTurnMetricModel

namespace CurveComplex.Hyperbolic

theorem vertexHalfTurn_unit_reflection (z : H2) :
    vertexHalfTurnEquiv (unitCircleReflectionEquiv z) = verticalReflectionEquiv z := by
  change verticalReflectionEquiv (unitCircleReflectionEquiv (unitCircleReflectionEquiv z)) = _
  rw [unitCircleReflection_involutive]

theorem vertexHalfTurn_fixes_normalized_vertex (p : H2) (hp : p.re = 0) (hi : p.im = 1) :
    vertexHalfTurnEquiv p = p := by
  change verticalReflectionEquiv (unitCircleReflectionEquiv p) = p
  rw [(unitCircleReflection_fixed_iff p).mpr (by rw [hp, hi]; norm_num),
    (verticalReflection_fixed_iff p).mpr hp]

theorem positive_quarter_halfTurn_distance_le (a b : H2)
    (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (hna : a.re ^ 2 + a.im ^ 2 ≤ 1) (hnb : b.re ^ 2 + b.im ^ 2 ≤ 1) :
    dist a b ≤ dist a (vertexHalfTurnEquiv b) := by
  apply (Real.cosh_strictMonoOn.le_iff_le dist_nonneg dist_nonneg).mp
  have hd : 0 < b.re ^ 2 + b.im ^ 2 := by nlinarith [b.im_pos]
  have hden : 0 < 2 * a.im * b.im := by positivity
  have hformula : Real.cosh (dist a (vertexHalfTurnEquiv b)) =
      ((a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2) + 2 * a.re * b.re + 1) /
        (2 * a.im * b.im) := by
    change Real.cosh (dist a (verticalReflectionEquiv (unitCircleReflectionEquiv b))) = _
    rw [UpperHalfPlane.cosh_dist', verticalReflection_re, verticalReflection_im,
      unitCircleReflection_re, unitCircleReflection_im]
    field_simp
    <;> ring
  rw [hformula, UpperHalfPlane.cosh_dist']
  rw [div_le_div_iff_of_pos_right hden]
  have hm := mul_nonneg (sub_nonneg.mpr hna) (sub_nonneg.mpr hnb)
  have hr := mul_nonneg ha hb
  nlinarith

theorem halfTurnMetricCone_positive_quarter_distance (a b : H2)
    (ha : 0 ≤ a.re) (hb : 0 ≤ b.re)
    (hna : a.re ^ 2 + a.im ^ 2 ≤ 1) (hnb : b.re ^ 2 + b.im ^ 2 ≤ 1) :
    dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone b) = dist a b := by
  rw [halfTurnMetricCone_distance]
  exact min_eq_left (positive_quarter_halfTurn_distance_le a b ha hb hna hnb)

theorem halfTurnMetricCone_cross_quarter_distance (a b : H2) :
    dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone (unitCircleReflectionEquiv b)) =
      min (dist a (verticalReflectionEquiv b)) (dist a (unitCircleReflectionEquiv b)) := by
  rw [halfTurnMetricCone_distance, vertexHalfTurn_unit_reflection, min_comm]

theorem halfTurnMetricCone_center_distance (a p : H2) (hp : p.re = 0) (hi : p.im = 1) :
    dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone p) = dist a p := by
  rw [halfTurnMetricCone_distance, vertexHalfTurn_fixes_normalized_vertex p hp hi, min_self]

theorem unit_reflection_halfTurn_commute (z : H2) :
    unitCircleReflectionEquiv (vertexHalfTurnEquiv z) =
      vertexHalfTurnEquiv (unitCircleReflectionEquiv z) := by
  change unitCircleReflectionEquiv (verticalReflectionEquiv (unitCircleReflectionEquiv z)) =
    verticalReflectionEquiv (unitCircleReflectionEquiv (unitCircleReflectionEquiv z))
  rw [vertex_reflections_commute]

theorem halfTurnMetricCone_unit_reflection_distance (a b : H2) :
    dist (toHalfTurnMetricCone (unitCircleReflectionEquiv a))
      (toHalfTurnMetricCone (unitCircleReflectionEquiv b)) =
      dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone b) := by
  rw [halfTurnMetricCone_distance, halfTurnMetricCone_distance,
    unitCircleReflectionEquiv.dist_eq, ← unit_reflection_halfTurn_commute,
    unitCircleReflectionEquiv.dist_eq]

theorem halfTurnMetricCone_halfTurn_eq (z : H2) :
    toHalfTurnMetricCone (vertexHalfTurnEquiv z) = toHalfTurnMetricCone z := by
  apply dist_eq_zero.mp
  rw [halfTurnMetricCone_distance]
  exact le_antisymm ((min_le_right _ _).trans_eq (dist_self _)) (le_min dist_nonneg dist_nonneg)

end CurveComplex.Hyperbolic
