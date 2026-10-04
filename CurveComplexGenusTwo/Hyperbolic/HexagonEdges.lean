import CurveComplexGenusTwo.Hyperbolic.ElementaryPolygon

namespace CurveComplex.Hyperbolic

/-! Endpoint membership for the metric segments used by `Hexagon.edge`. -/

theorem Hexagon.left_mem_edge (P : Hexagon) (i : Fin 6) :
    P.vertex i ∈ P.edge i := by
  simp [Hexagon.edge]

theorem Hexagon.right_mem_edge (P : Hexagon) (i : Fin 6) :
    P.vertex (i + 1) ∈ P.edge i := by
  simp [Hexagon.edge, dist_comm]

end CurveComplex.Hyperbolic
