import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import CurveComplexGenusTwo.Hyperbolic.HyperbolicSeamWave11

namespace CurveComplex.Hyperbolic
open Set

/-- Reflection in the full hyperbolic geodesic containing a genuine metric segment. -/
theorem metric_segment_has_reflection (a b : H2) :
    ∃ r : H2 ≃ᵢ H2,
      Function.Involutive r ∧ r a = a ∧ r b = b ∧
      (∀ z, dist a z + dist z b = dist a b → r z = z) ∧
      ∃ z, r z ≠ z := by
  obtain ⟨e, ha, hb⟩ := exists_pair_vertical_isometry a b
  let c := IdealHexagonDouble.sideZeroAbscissa
  let T := realTranslationIsometry c
  let E := e.trans T
  let V := IdealHexagonDouble.sideZeroReflectionEquiv
  let r := E.trans (V.trans E.symm)
  have hE (z : H2) : (E z).re = c + (e z).re := by
    simp [E, T, realTranslationIsometry, UpperHalfPlane.vadd_re]
  have hra (z : H2) (hz : (e z).re = 0) : r z = z := by
    have hv : V (E z) = E z :=
      (IdealHexagonDouble.sideZeroReflection_fixed_iff (E z)).mpr (by
        change (E z).re = c
        rw [hE, hz, add_zero])
    change E.symm (V (E z)) = z
    rw [hv, E.symm_apply_apply]
  refine ⟨r, ?_, hra a ha, hra b hb, ?_, ?_⟩
  · intro z
    change E.symm (V (E (E.symm (V (E z))))) = z
    rw [E.apply_symm_apply]
    change E.symm (IdealHexagonDouble.sideZeroReflection
      (IdealHexagonDouble.sideZeroReflection (E z))) = z
    rw [IdealHexagonDouble.sideZeroReflection_involutive, E.symm_apply_apply]
  · intro z hz
    apply hra
    have heq : dist (e a) (e z) + dist (e z) (e b) = dist (e a) (e b) := by
      simpa only [e.dist_eq] using hz
    exact (metric_segment_on_vertical (ha.trans hb.symm) heq).trans ha
  · let w : H2 := ⟨⟨c + 1, 1⟩, by norm_num⟩
    refine ⟨E.symm w, ?_⟩
    intro hh
    have he : V w = w := by
      have := congrArg E hh
      simpa only [r, IsometryEquiv.trans_apply, E.apply_symm_apply] using this
    have hc : w.re = c := (IdealHexagonDouble.sideZeroReflection_fixed_iff w).mp he
    change c + 1 = c at hc
    linarith

theorem Hexagon.actual_edge_reflection (P : Hexagon) (i : Fin 6) :
    ∃ r : H2 ≃ᵢ H2, Function.Involutive r ∧
      (∀ z ∈ P.edge i, r z = z) ∧ ∃ z, r z ≠ z := by
  obtain ⟨r, hr, _, _, hedge, hn⟩ :=
    metric_segment_has_reflection (P.vertex i) (P.vertex (i + 1))
  exact ⟨r, hr, hedge, hn⟩

end CurveComplex.Hyperbolic
