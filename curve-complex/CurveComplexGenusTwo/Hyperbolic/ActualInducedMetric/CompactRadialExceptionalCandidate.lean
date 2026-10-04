import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactRadialBoundaryNullCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactRadialSectorCoordinatesCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal
open IdealHexagonDouble

noncomputable def compactRadialExceptional : Set H2 := ⋃i : Fin 6,
  h2RotationIso i '' {z | (cayley z:ℂ).im=0 ∨
    (cayley z:ℂ).re=Real.sqrt 3*|(cayley z:ℂ).im|}

theorem rotation_inverse_cayley_coordinate (i : Fin 6) (z : H2) :
    (cayley ((h2RotationIso i).symm z):ℂ)=star (idealHexagonVertex i)*(cayley z:ℂ) := by
  have h := h2Rotation_cayley i ((h2RotationIso i).symm z)
  change (cayley (h2RotationIso i ((h2RotationIso i).symm z)):ℂ)=_ at h
  rw [(h2RotationIso i).apply_symm_apply] at h
  have h' := congrArg (fun w : ℂ => star (idealHexagonVertex i)*w) h
  rw [←mul_assoc,ideal_hexagon_vertex_star_unit,one_mul] at h'
  exact h'.symm

theorem compact_radial_exceptional_mem_iff (z : H2) : z∈compactRadialExceptional ↔
    ∃i : Fin 6, (star (idealHexagonVertex i)*(cayley z:ℂ)).im=0 ∨
      (star (idealHexagonVertex i)*(cayley z:ℂ)).re=
        Real.sqrt 3*|(star (idealHexagonVertex i)*(cayley z:ℂ)).im| := by
  simp only [compactRadialExceptional,mem_iUnion]
  constructor
  · rintro ⟨i,y,hy,rfl⟩
    refine ⟨i,?_⟩
    have hc : star (idealHexagonVertex i)*(cayley (h2RotationIso i y):ℂ)=(cayley y:ℂ) := by
      change star (idealHexagonVertex i)*(cayley (h2Rotation i y):ℂ)=_
      rw [h2Rotation_cayley,←mul_assoc,ideal_hexagon_vertex_star_unit,one_mul]
    rw [hc]
    exact hy
  · rintro ⟨i,hi⟩
    refine ⟨i,(h2RotationIso i).symm z,?_,(h2RotationIso i).apply_symm_apply z⟩
    change (cayley ((h2RotationIso i).symm z):ℂ).im=0 ∨ _
    rw [rotation_inverse_cayley_coordinate]
    exact hi

theorem compact_radial_exceptional_normalized_area_zero :
    (μHE[2] : Measure H2) compactRadialExceptional=0 := by
  apply measure_iUnion_null
  intro i
  rw [hyperbolic_isometry_normalized_area_image]
  exact cayley_half_wedge_boundaries_normalized_area_zero

end CurveComplex.Hyperbolic
