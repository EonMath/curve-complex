import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalClosedQuarter
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactQuarterOrientation

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_positive_vertex_quarter (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ closure regularHexagonRegion.interior ↔
          0 ≤ (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 ≤ 1) ∧
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ regularHexagonRegion.interior ↔
          0 < (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 < 1) ∧
      (∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
        z ∈ frontier regularHexagonRegion.interior ↔
          0 ≤ (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 ≤ 1 ∧
            ((e z).re = 0 ∨ (e z).re ^ 2 + (e z).im ^ 2 = 1)) := by
  obtain ⟨f, hp, hi, r, hr, a, b, hclosed, hinside⟩ :=
    regularHexagon_actual_closed_vertex_quarter i
  let e := f.trans (quarterOrientationIsometry a b)
  have hpfix : e (regularHexagonCandidate.vertex i) = f (regularHexagonCandidate.vertex i) :=
    quarterOrientation_fixes_normalized_vertex a b _ hp hi
  have hcl : ∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
      z ∈ closure regularHexagonRegion.interior ↔
        0 ≤ (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 ≤ 1 := by
    intro z hz
    exact (hclosed z hz).trans (quarterOrientation_closed a b (f z)).symm
  have hin : ∀ z ∈ Metric.ball (regularHexagonCandidate.vertex i) r,
      z ∈ regularHexagonRegion.interior ↔
        0 < (e z).re ∧ (e z).re ^ 2 + (e z).im ^ 2 < 1 := by
    intro z hz
    exact (hinside z hz).trans (quarterOrientation_strict a b (f z)).symm
  refine ⟨e, by rw [hpfix]; exact hp, by rw [hpfix]; exact hi,
    r, hr, hcl, hin, ?_⟩
  intro z hz
  rw [frontier, regularHexagonRegion.open_interior.interior_eq,
    Set.mem_diff, hcl z hz, hin z hz]
  constructor
  · rintro ⟨⟨hreal, hnorm⟩, hnot⟩
    refine ⟨hreal, hnorm, ?_⟩
    by_contra h
    have hrealne : (e z).re ≠ 0 := fun he => h (Or.inl he)
    have hnormne : (e z).re ^ 2 + (e z).im ^ 2 ≠ 1 := fun he => h (Or.inr he)
    exact hnot ⟨lt_of_le_of_ne hreal (Ne.symm hrealne),
      lt_of_le_of_ne hnorm hnormne⟩
  · rintro ⟨hreal, hnorm, haxis⟩
    refine ⟨⟨hreal, hnorm⟩, ?_⟩
    rintro ⟨hr', hn'⟩
    rcases haxis with h | h <;> linarith

end CurveComplex.Hyperbolic
