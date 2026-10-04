import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactQuarterOrientation

namespace CurveComplex.Hyperbolic

noncomputable def vertexHalfTurnEquiv : H2 ≃ᵢ H2 :=
  unitCircleReflectionEquiv.trans verticalReflectionEquiv

theorem vertexHalfTurn_involutive : Function.Involutive vertexHalfTurnEquiv := by
  intro z
  change verticalReflectionEquiv (unitCircleReflectionEquiv
    (verticalReflectionEquiv (unitCircleReflectionEquiv z))) = z
  rw [vertex_reflections_commute, unitCircleReflection_involutive,
    verticalReflection_involutive]

private theorem halfTurn_cross_distance_symmetry (a b : H2) :
    dist a (vertexHalfTurnEquiv b) = dist b (vertexHalfTurnEquiv a) := by
  calc
    _ = dist (vertexHalfTurnEquiv a) (vertexHalfTurnEquiv (vertexHalfTurnEquiv b)) :=
      (vertexHalfTurnEquiv.dist_eq _ _).symm
    _ = dist (vertexHalfTurnEquiv a) b := by rw [vertexHalfTurn_involutive b]
    _ = dist b (vertexHalfTurnEquiv a) := dist_comm _ _

structure HalfTurnPseudoPlane where
  point : H2

noncomputable instance halfTurnPseudoMetric : PseudoMetricSpace HalfTurnPseudoPlane where
  dist a b := min (dist a.point b.point) (dist a.point (vertexHalfTurnEquiv b.point))
  dist_self a := by simp only [dist_self]; exact min_eq_left dist_nonneg
  dist_comm a b := by rw [dist_comm a.point b.point, halfTurn_cross_distance_symmetry]
  dist_triangle a b c := by
    rcases le_total (dist a.point b.point) (dist a.point (vertexHalfTurnEquiv b.point)) with hab | hab <;>
      rcases le_total (dist b.point c.point) (dist b.point (vertexHalfTurnEquiv c.point)) with hbc | hbc
    · rw [min_eq_left hab, min_eq_left hbc]
      exact (min_le_left _ _).trans (dist_triangle _ _ _)
    · rw [min_eq_left hab, min_eq_right hbc]
      exact (min_le_right _ _).trans (dist_triangle _ _ _)
    · rw [min_eq_right hab, min_eq_left hbc]
      apply (min_le_right _ _).trans
      have ht := dist_triangle a.point (vertexHalfTurnEquiv b.point) (vertexHalfTurnEquiv c.point)
      rwa [vertexHalfTurnEquiv.dist_eq] at ht
    · rw [min_eq_right hab, min_eq_right hbc]
      apply (min_le_left _ _).trans
      have ht := dist_triangle a.point (vertexHalfTurnEquiv b.point) c.point
      rw [dist_comm (vertexHalfTurnEquiv b.point) c.point,
        halfTurn_cross_distance_symmetry c.point b.point] at ht
      exact ht

abbrev HalfTurnMetricCone := SeparationQuotient HalfTurnPseudoPlane

noncomputable def toHalfTurnMetricCone (z : H2) : HalfTurnMetricCone :=
  SeparationQuotient.mk ⟨z⟩

theorem halfTurnMetricCone_distance (a b : H2) :
    dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone b) =
      min (dist a b) (dist a (vertexHalfTurnEquiv b)) := by
  exact SeparationQuotient.dist_mk _ _

theorem halfTurnMetricCone_projection_distance_le (a b : H2) :
    dist (toHalfTurnMetricCone a) (toHalfTurnMetricCone b) ≤ dist a b := by
  rw [halfTurnMetricCone_distance]
  exact min_le_left _ _

end CurveComplex.Hyperbolic
