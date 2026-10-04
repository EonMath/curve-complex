import CurveComplexGenusTwo.Hyperbolic.CompactPolygonGeometry

namespace CurveComplex.Hyperbolic

-- These two definitions are copied verbatim from the approved scaffold.
-- Integration must reuse its existing definitions, not introduce duplicates.
def Hexagon.IsEmbedded (P : Hexagon) : Prop :=
  ∀ i j : Fin 6, i ≠ j →
    P.edge i ∩ P.edge j ⊆
      ({P.vertex i, P.vertex (i + 1)} : Set H2) ∩
      ({P.vertex j, P.vertex (j + 1)} : Set H2)

def Hexagon.IsRegularRight (P : Hexagon) : Prop :=
  P.IsEmbedded ∧
  (∀ i j, dist (P.vertex i) (P.vertex (i + 1)) =
    dist (P.vertex j) (P.vertex (j + 1))) ∧
  (∀ i, IsRightAngle (P.vertex (i - 1)) (P.vertex i)
    (P.vertex (i + 1)))

theorem regularHexagonCandidate_isRegularRight :
    regularHexagonCandidate.IsRegularRight := by
  refine ⟨regularHexagonCandidate_embedded, ?_, regularHexagonCandidate_right_angles⟩
  exact regularHexagon_adjacent_dist_eq

theorem exists_regular_right_hexagon : ∃ P : Hexagon, P.IsRegularRight :=
  ⟨regularHexagonCandidate, regularHexagonCandidate_isRegularRight⟩

end CurveComplex.Hyperbolic
