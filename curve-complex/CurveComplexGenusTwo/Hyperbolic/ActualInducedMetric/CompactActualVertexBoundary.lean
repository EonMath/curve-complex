import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexGeodesics
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexIsolation

namespace CurveComplex.Hyperbolic
open Set Topology

theorem HexagonRegion.actual_right_angle_vertex_boundary_coordinates
    {P : Hexagon} (R : HexagonRegion P) (hP : P.IsRegularRight) (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (P.vertex i)).re = 0 ∧ (e (P.vertex i)).im = 1 ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Metric.ball (P.vertex i) ε,
        z ∈ frontier R.interior →
          (e z).re = 0 ∨ (e z).re ^ 2 + (e z).im ^ 2 = 1 := by
  have hqp : P.vertex (i - 1) ≠ P.vertex i := by
    intro he
    have hi := P.injective he
    fin_cases i <;> norm_num at hi
  obtain ⟨e, hp, hi, hprev, hnext⟩ := actual_right_angle_incident_geodesics
    (P.vertex (i - 1)) (P.vertex i) (P.vertex (i + 1)) (hP.2.2 i) hqp
  obtain ⟨ε, he, hiso⟩ := P.embedded_vertex_local_isolation hP.1 i
  refine ⟨e, hp, hi, ε, he, ?_⟩
  intro z hz hf
  rw [R.boundary_is_edges] at hf
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hf
  by_cases hji : j = i
  · subst j
    exact Or.inr (hnext z hj)
  by_cases hji' : j = i - 1
  · subst j
    have hi' : i - 1 + 1 = i := by
      fin_cases i <;> rfl
    change dist (P.vertex (i - 1)) z +
      dist z (P.vertex (i - 1 + 1)) = _ at hj
    rw [hi'] at hj
    exact Or.inl (hprev z (by simpa only [dist_comm, add_comm] using hj))
  exact False.elim (Set.disjoint_left.mp (hiso j hji hji') hz hj)

end CurveComplex.Hyperbolic
