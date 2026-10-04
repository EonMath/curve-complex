import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalQuarterUniqueness
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactVertexAxesInterior

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_exactly_one_occupied_quarter (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∃ a b : Bool,
        vertexQuarter e (regularHexagonCandidate.vertex i) r a b ⊆ regularHexagonRegion.interior ∧
        ∀ a' b' : Bool, a' ≠ a ∨ b' ≠ b →
          vertexQuarter e (regularHexagonCandidate.vertex i) r a' b' ⊆
            (closure regularHexagonRegion.interior)ᶜ := by
  classical
  obtain ⟨e, hp, hi, r, hr, hd, hu⟩ := regularHexagon_actual_occupied_quarter_unique i
  let p := regularHexagonCandidate.vertex i
  have hne : (regularHexagonRegion.interior ∩ Metric.ball p r).Nonempty := by
    have hm := mem_closure_iff_nhds.mp
      (hexagon_vertex_mem_closure regularHexagonCandidate regularHexagonRegion i)
      (Metric.ball p r) (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    simpa only [Set.inter_comm] using hm
  let U := e '' (regularHexagonRegion.interior ∩ Metric.ball p r)
  have hU : IsOpen U := e.toHomeomorph.isOpenMap _
    (regularHexagonRegion.open_interior.inter Metric.isOpen_ball)
  obtain ⟨z, hz, hzre, hznorm⟩ := open_set_contains_point_off_vertex_axes U hU (hne.image e)
  obtain ⟨w, hw, hew⟩ := hz
  let a : Bool := decide (0 < z.re)
  let b : Bool := decide (z.re ^ 2 + z.im ^ 2 < 1)
  have ha : if a then 0 < z.re else z.re < 0 := by
    dsimp [a]
    by_cases h : 0 < z.re
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ite_eq_right]
      exact lt_of_le_of_ne (le_of_not_gt h) hzre
  have hb : if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2 := by
    dsimp [b]
    by_cases h : z.re ^ 2 + z.im ^ 2 < 1
    · simp [h]
    · simp only [h, decide_false, Bool.false_eq_true, ite_eq_right]
      exact lt_of_le_of_ne (le_of_not_gt h) hznorm.symm
  have hwq : w ∈ vertexQuarter e p r a b := by
    change e w ∈ Metric.ball (e p) r ∩ {u : H2 |
      (if a then 0 < u.re else u.re < 0) ∧
      (if b then u.re ^ 2 + u.im ^ 2 < 1 else 1 < u.re ^ 2 + u.im ^ 2)}
    refine ⟨?_, ?_⟩
    · simpa only [Metric.mem_ball, e.dist_eq] using hw.2
    · rw [hew]
      exact ⟨ha, hb⟩
  have hocc : vertexQuarter e p r a b ⊆ regularHexagonRegion.interior := by
    rcases hd a b with h | h
    · exact h
    · exact False.elim (h hwq (subset_closure hw.1))
  refine ⟨e, hp, hi, r, hr, a, b, hocc, ?_⟩
  intro a' b' hneq
  rcases hd a' b' with h | h
  · have heq := hu a b a' b' hocc h
    exact False.elim (hneq.elim (fun h => h heq.1.symm) (fun h => h heq.2.symm))
  · exact h

end CurveComplex.Hyperbolic
