import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalOccupiedQuarter
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactOpenQuarterIdentification

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_vertex_quarter (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∃ a b : Bool, ∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ regularHexagonRegion.interior ↔
          (if a then 0 < (e z).re else (e z).re < 0) ∧
          (if b then (e z).re ^ 2 + (e z).im ^ 2 < 1
            else 1 < (e z).re ^ 2 + (e z).im ^ 2) := by
  classical
  obtain ⟨e, hp, hi, r, hr, a, b, hocc, hother⟩ :=
    regularHexagon_actual_exactly_one_occupied_quarter i
  let p := regularHexagonCandidate.vertex i
  let U := e '' (regularHexagonRegion.interior ∩ Metric.ball p r)
  have hU : IsOpen U := e.toHomeomorph.isOpenMap _
    (regularHexagonRegion.open_interior.inter Metric.isOpen_ball)
  have hball : U ⊆ Metric.ball (e p) r := by
    rintro z ⟨w, hw, rfl⟩
    simpa only [Metric.mem_ball, e.dist_eq] using hw.2
  have hoff : ∀ z ∈ U, z.re ≠ 0 → z.re ^ 2 + z.im ^ 2 ≠ 1 →
      (if a then 0 < z.re else z.re < 0) ∧
      (if b then z.re ^ 2 + z.im ^ 2 < 1 else 1 < z.re ^ 2 + z.im ^ 2) := by
    intro z hz hzre hznorm
    obtain ⟨w, hw, hew⟩ := hz
    obtain ⟨a', b', ha', hb'⟩ := off_vertex_axes_quarter_classification z hzre hznorm
    have hwq : w ∈ vertexQuarter e p r a' b' := by
      change e w ∈ Metric.ball (e p) r ∩ {u : H2 |
        (if a' then 0 < u.re else u.re < 0) ∧
        (if b' then u.re ^ 2 + u.im ^ 2 < 1 else 1 < u.re ^ 2 + u.im ^ 2)}
      refine ⟨?_, ?_⟩
      · simpa only [Metric.mem_ball, e.dist_eq] using hw.2
      · rw [hew]
        exact ⟨ha', hb'⟩
    have hab : a' = a ∧ b' = b := by
      by_contra h
      have hneq : a' ≠ a ∨ b' ≠ b := by tauto
      exact hother a' b' hneq hwq (subset_closure hw.1)
    simpa only [hab.1, hab.2] using And.intro ha' hb'
  have hsub := open_set_vertex_quarter_identification U hU (e p) r a b hball hoff
  refine ⟨e, hp, hi, r, hr, a, b, ?_⟩
  intro z hz
  constructor
  · intro hzi
    exact (hsub ⟨z, ⟨hzi, hz⟩, rfl⟩).2
  · intro hcoords
    apply hocc
    change e z ∈ Metric.ball (e p) r ∩ {u : H2 |
      (if a then 0 < u.re else u.re < 0) ∧
      (if b then u.re ^ 2 + u.im ^ 2 < 1 else 1 < u.re ^ 2 + u.im ^ 2)}
    refine ⟨?_, hcoords⟩
    simpa only [Metric.mem_ball, e.dist_eq] using hz

end CurveComplex.Hyperbolic
