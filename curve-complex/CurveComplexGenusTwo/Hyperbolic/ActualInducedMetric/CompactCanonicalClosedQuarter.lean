import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalVertexQuarterModel
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactClosedQuarterModel

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_closed_vertex_quarter (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧ ∃ a b : Bool,
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ closure regularHexagonRegion.interior ↔
          (if a then 0 ≤ (e z).re else (e z).re ≤ 0) ∧
          (if b then (e z).re ^ 2 + (e z).im ^ 2 ≤ 1
            else 1 ≤ (e z).re ^ 2 + (e z).im ^ 2)) ∧
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ regularHexagonRegion.interior ↔
          (if a then 0 < (e z).re else (e z).re < 0) ∧
          (if b then (e z).re ^ 2 + (e z).im ^ 2 < 1
            else 1 < (e z).re ^ 2 + (e z).im ^ 2)) := by
  classical
  obtain ⟨e, hp, hi, r, hr, a, b, hlocal⟩ := regularHexagon_actual_vertex_quarter i
  let p := regularHexagonCandidate.vertex i
  let A := regularHexagonRegion.interior ∩ Metric.ball p r
  let Q : Set H2 := Metric.ball (e p) r ∩ {w : H2 |
    (if a then 0 < w.re else w.re < 0) ∧
    (if b then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)}
  have himage : e '' A = Q := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨by simpa only [Metric.mem_ball, e.dist_eq] using hz.2,
        (hlocal z hz.2).mp hz.1⟩
    · intro hw
      have hwb : e.symm w ∈ Metric.ball p r := by
        simpa only [Metric.mem_ball, ← e.dist_eq (e.symm w) p, e.apply_symm_apply] using hw.1
      refine ⟨e.symm w, ⟨?_, hwb⟩, e.apply_symm_apply w⟩
      apply (hlocal (e.symm w) hwb).mpr
      rw [e.apply_symm_apply]
      exact hw.2
  refine ⟨e, hp, hi, r, hr, a, b, ?_, hlocal⟩
  intro z hz
  have hzball : e z ∈ Metric.ball (e p) r := by
    simpa only [Metric.mem_ball, e.dist_eq] using hz
  have hcl : z ∈ closure regularHexagonRegion.interior ↔ e z ∈ closure Q := by
    have hecl : e '' closure A = closure Q := by
      change e.toHomeomorph '' closure A = closure Q
      rw [e.toHomeomorph.image_closure]
      exact congrArg closure himage
    constructor
    · intro hzc
      have hza : z ∈ closure A := Metric.isOpen_ball.closure_inter ⟨hzc, hz⟩
      rw [← hecl]
      exact ⟨z, hza, rfl⟩
    · intro hqc
      rw [← hecl] at hqc
      obtain ⟨w, hw, hew⟩ := hqc
      have hwz : w = z := e.injective hew
      subst w
      exact closure_mono (Set.inter_subset_left : A ⊆ regularHexagonRegion.interior) hw
  exact hcl.trans (normalized_closed_quarter_model (e p) hp hi r hr a b (e z) hzball)

end CurveComplex.Hyperbolic
