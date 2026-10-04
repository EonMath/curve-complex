import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactJordanRegionUniqueness
import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion
import CurveComplexGenusTwo.Hyperbolic.RotationInvarianceWave11

namespace CurveComplex.Hyperbolic
open Set Topology
open IdealHexagonDouble

theorem regular_hexagon_rotation_vertex (i j : Fin 6) :
    h2RotationIso i (regularHexagonCandidate.vertex j) =
      regularHexagonCandidate.vertex (i + j) := by
  apply cayley_injective
  apply Subtype.ext
  change (cayley (h2Rotation i (regularHexagonCandidate.vertex j)) : ℂ) = _
  rw [h2Rotation_cayley]
  change idealHexagonVertex i * (cayley (regularHexagonH2Point j) : ℂ) =
    (cayley (regularHexagonH2Point (i + j)) : ℂ)
  simp only [regularHexagonH2Point, cayley_cayleyInverse, regularHexagonDiscPoint]
  rw [← idealVertex_mul]
  ring

theorem regular_hexagon_rotation_edge (i j : Fin 6) :
    h2RotationIso i '' regularHexagonCandidate.edge j =
      regularHexagonCandidate.edge (i + j) := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    change dist (regularHexagonCandidate.vertex (i + j)) (h2RotationIso i x) +
      dist (h2RotationIso i x) (regularHexagonCandidate.vertex (i + j + 1)) = _
    rw [← regular_hexagon_rotation_vertex i j,
      show i + j + 1 = i + (j + 1) by ac_rfl,
      ← regular_hexagon_rotation_vertex i (j + 1)]
    simpa only [Hexagon.edge, mem_ofPred_eq, (h2RotationIso i).dist_eq] using hx
  · intro hz
    refine ⟨(h2RotationIso i).symm z, ?_, (h2RotationIso i).apply_symm_apply z⟩
    change dist (regularHexagonCandidate.vertex j) ((h2RotationIso i).symm z) +
      dist ((h2RotationIso i).symm z) (regularHexagonCandidate.vertex (j + 1)) = _
    rw [← (h2RotationIso i).dist_eq (regularHexagonCandidate.vertex j) ((h2RotationIso i).symm z),
      ← (h2RotationIso i).dist_eq ((h2RotationIso i).symm z) (regularHexagonCandidate.vertex (j + 1)),
      ← (h2RotationIso i).dist_eq (regularHexagonCandidate.vertex j) (regularHexagonCandidate.vertex (j + 1))]
    simp only [(h2RotationIso i).apply_symm_apply, regular_hexagon_rotation_vertex]
    simpa only [Hexagon.edge, mem_ofPred_eq, add_assoc] using hz

theorem regular_hexagon_rotation_frontier (i : Fin 6) :
    h2RotationIso i '' frontier regularHexagonRegion.interior =
      frontier regularHexagonRegion.interior := by
  rw [regularHexagonRegion.boundary_is_edges, image_iUnion]
  simp_rw [regular_hexagon_rotation_edge]
  ext z
  simp only [mem_iUnion]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨i + j, hj⟩
  · rintro ⟨j, hj⟩
    refine ⟨j - i, ?_⟩
    have hidx : i + (j - i) = j := by fin_cases i <;> fin_cases j <;> decide
    simpa only [hidx] using hj

theorem regular_hexagon_rotation_interior (i : Fin 6) :
    h2RotationIso i '' regularHexagonRegion.interior = regularHexagonRegion.interior := by
  let e := hyperbolicPlaneHomeomorph
  have h₁ := regularHexagonRegion.image_interior_eq_inside
    regularHexagonCandidate_embedded ((h2RotationIso i).toHomeomorph.trans e)
  have h₂ := regularHexagonRegion.image_interior_eq_inside regularHexagonCandidate_embedded e
  have hf := regular_hexagon_rotation_frontier i
  have h₁' : e '' (h2RotationIso i '' regularHexagonRegion.interior) =
      Schoenflies.inside (e '' frontier regularHexagonRegion.interior) := by
    change (fun x => e (h2RotationIso i x)) '' regularHexagonRegion.interior =
      Schoenflies.inside ((fun x => e (h2RotationIso i x)) '' frontier regularHexagonRegion.interior) at h₁
    have hc (s : Set H2) : (fun x => e (h2RotationIso i x)) '' s = e '' (h2RotationIso i '' s) := (image_image _ _ _).symm
    rw [hc, hc, hf] at h₁
    exact h₁
  exact e.injective.image_injective (h₁'.trans h₂.symm)

end CurveComplex.Hyperbolic
