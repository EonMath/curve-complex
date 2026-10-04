import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactOccupiedQuarterSigns
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalCircumball

namespace CurveComplex.Hyperbolic
open Set Topology

theorem regularHexagon_actual_occupied_quarter_unique (i : Fin 6) :
    ∃ e : H2 ≃ᵢ H2, (e (regularHexagonCandidate.vertex i)).re = 0 ∧
      (e (regularHexagonCandidate.vertex i)).im = 1 ∧
      ∃ r : ℝ, 0 < r ∧
        (∀ positive inner : Bool,
          vertexQuarter e (regularHexagonCandidate.vertex i) r positive inner ⊆ regularHexagonRegion.interior ∨
          vertexQuarter e (regularHexagonCandidate.vertex i) r positive inner ⊆
            (closure regularHexagonRegion.interior)ᶜ) ∧
        ∀ a b a' b' : Bool,
          vertexQuarter e (regularHexagonCandidate.vertex i) r a b ⊆ regularHexagonRegion.interior →
          vertexQuarter e (regularHexagonCandidate.vertex i) r a' b' ⊆ regularHexagonRegion.interior →
          a = a' ∧ b = b' := by
  obtain ⟨e, hp, hi, r, hr, hd⟩ :=
    regularHexagonRegion.actual_vertex_sector_dichotomy regularHexagonCandidate_isRegularRight i
  refine ⟨e, hp, hi, r, hr, hd, ?_⟩
  have hbound (a b : Bool)
      (hocc : vertexQuarter e (regularHexagonCandidate.vertex i) r a b ⊆ regularHexagonRegion.interior) :
      ∀ z ∈ Metric.ball (e (regularHexagonCandidate.vertex i)) r ∩ {w : H2 |
        (if a then 0 < w.re else w.re < 0) ∧
        (if b then w.re ^ 2 + w.im ^ 2 < 1 else 1 < w.re ^ 2 + w.im ^ 2)},
        Real.cosh (dist (e regularHexagonCenter) z) ≤
          Real.cosh (dist (e regularHexagonCenter) (e (regularHexagonCandidate.vertex i))) := by
    intro z hz
    have hw : e.symm z ∈ vertexQuarter e (regularHexagonCandidate.vertex i) r a b := by
      simpa only [vertexQuarter, Set.mem_preimage, e.apply_symm_apply] using hz
    have hb := regularHexagon_closed_region_circumball (e.symm z) (subset_closure (hocc hw))
    rw [← regularHexagon_center_cosh_vertex i] at hb
    have hez : dist (e regularHexagonCenter) z = dist regularHexagonCenter (e.symm z) := by
      simpa only [e.apply_symm_apply] using e.dist_eq regularHexagonCenter (e.symm z)
    rw [hez, e.dist_eq]
    exact hb
  intro a b a' b' hocc hocc'
  have ha := occupied_quarter_horizontal_sign (e regularHexagonCenter)
    (e (regularHexagonCandidate.vertex i)) hp hi r hr a b (hbound a b hocc)
  have ha' := occupied_quarter_horizontal_sign (e regularHexagonCenter)
    (e (regularHexagonCandidate.vertex i)) hp hi r hr a' b' (hbound a' b' hocc')
  have hb := occupied_quarter_vertical_sign (e regularHexagonCenter)
    (e (regularHexagonCandidate.vertex i)) hp hi r hr a b (hbound a b hocc)
  have hb' := occupied_quarter_vertical_sign (e regularHexagonCenter)
    (e (regularHexagonCandidate.vertex i)) hp hi r hr a' b' (hbound a' b' hocc')
  constructor
  · cases a <;> cases a' <;> first | rfl | (simp at ha ha'; linarith)
  · cases b <;> cases b' <;> first | rfl | (simp at hb hb'; linarith)

end CurveComplex.Hyperbolic
