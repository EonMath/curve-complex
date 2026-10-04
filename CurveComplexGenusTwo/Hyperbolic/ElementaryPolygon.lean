import CurveComplexGenusTwo.Hyperbolic.Cayley

namespace CurveComplex.Hyperbolic

open scoped UpperHalfPlane

structure Hexagon where
  vertex : Fin 6 → H2
  injective : Function.Injective vertex

def Hexagon.edge (P : Hexagon) (i : Fin 6) : Set H2 :=
  {z | dist (P.vertex i) z + dist z (P.vertex (i + 1)) =
    dist (P.vertex i) (P.vertex (i + 1))}

structure HexagonRegion (P : Hexagon) where
  interior : Set H2
  open_interior : IsOpen interior
  connected_interior : IsConnected interior
  nonempty_interior : interior.Nonempty
  bounded_interior : Bornology.IsBounded interior
  boundary_is_edges : frontier interior = ⋃ i : Fin 6, P.edge i

abbrev ClosedPolygon {P : Hexagon} (R : HexagonRegion P) :=
  {z : H2 // z ∈ closure R.interior}

abbrev PolygonBoundary {P : Hexagon} (R : HexagonRegion P) :=
  {z : ClosedPolygon R // (z : H2) ∈ frontier R.interior}

noncomputable instance polygonBoundary_nonempty {P : Hexagon}
    (R : HexagonRegion P) : Nonempty (PolygonBoundary R) := by
  have hv : P.vertex 0 ∈ frontier R.interior := by
    rw [R.boundary_is_edges]
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    simp [Hexagon.edge]
  exact ⟨⟨⟨P.vertex 0, frontier_subset_closure hv⟩, hv⟩⟩

def boundaryInclusion {P : Hexagon} (R : HexagonRegion P) :
    PolygonBoundary R → ClosedPolygon R := Subtype.val

theorem boundaryInclusion_isometry {P : Hexagon} (R : HexagonRegion P) :
    Isometry (boundaryInclusion R) := by
  exact isometry_subtype_coe

theorem hexagon_vertex_mem_closure (P : Hexagon)
    (R : HexagonRegion P) (i : Fin 6) :
    P.vertex i ∈ closure R.interior := by
  apply frontier_subset_closure
  rw [R.boundary_is_edges]
  refine Set.mem_iUnion.mpr ⟨i, ?_⟩
  simp [Hexagon.edge]

end CurveComplex.Hyperbolic
