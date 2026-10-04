import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactCanonicalRadialPieceIsometryCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSixRootWedgeDisjointCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal
open IdealHexagonDouble

noncomputable def compactRadialSectorIsometry (i : Fin 6) (b : Bool) : H2 ≃ᵢ H2 :=
  (if b then IsometryEquiv.refl H2 else verticalReflectionEquiv).trans (h2RotationIso i)

def compactRadialFirstPiece : Set H2 := {z | z∈regularHexagonRegion.interior ∧
  0<(cayley z:ℂ).im ∧ Real.sqrt 3*(cayley z:ℂ).im<(cayley z:ℂ).re}

noncomputable def compactRadialSector (i : Fin 6) (b : Bool) : Set H2 :=
  compactRadialSectorIsometry i b '' compactRadialFirstPiece

theorem compact_radial_sector_area (i : Fin 6) (b : Bool) :
    (μHE[2] : Measure H2) (compactRadialSector i b)=ENNReal.ofReal (Real.pi/12) := by
  exact regular_hexagon_radial_piece_isometric_area (compactRadialSectorIsometry i b)

theorem compact_radial_sector_isOpen (i : Fin 6) (b : Bool) : IsOpen (compactRadialSector i b) := by
  apply (compactRadialSectorIsometry i b).toHomeomorph.isOpenMap
  exact regularHexagonRegion.open_interior.inter
    ((isOpen_lt continuous_const (Complex.continuous_im.comp (continuous_subtype_val.comp cayley_continuous))).inter
    (isOpen_lt (continuous_const.mul (Complex.continuous_im.comp (continuous_subtype_val.comp cayley_continuous)))
      (Complex.continuous_re.comp (continuous_subtype_val.comp cayley_continuous))))

theorem compact_radial_sector_is_subset (i : Fin 6) (b : Bool) :
    compactRadialSector i b ⊆ regularHexagonRegion.interior := by
  rintro z ⟨y,hy,rfl⟩
  apply (show h2RotationIso i '' regularHexagonRegion.interior=regularHexagonRegion.interior from regular_hexagon_rotation_interior i) ▸
    (show h2RotationIso i ((if b then IsometryEquiv.refl H2 else verticalReflectionEquiv) y) ∈
      h2RotationIso i '' regularHexagonRegion.interior from ?_)
  refine ⟨_,?_,rfl⟩
  cases b
  · exact (regular_hexagon_reflection_mem_interior y).mpr hy.1
  · exact hy.1

end CurveComplex.Hyperbolic
