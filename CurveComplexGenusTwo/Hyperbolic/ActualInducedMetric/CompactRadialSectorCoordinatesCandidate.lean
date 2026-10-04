import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactTwelveRadialSectorsCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open IdealHexagonDouble

theorem ideal_hexagon_vertex_star_unit (i : Fin 6) :
    star (idealHexagonVertex i)*idealHexagonVertex i=1 := by
  have hn : ‖idealHexagonVertex i‖=1 := by
    simpa only [Metric.mem_sphere,dist_zero_right] using idealHexagonVertex_mem_circle i
  simpa [Complex.star_def,hn] using (RCLike.conj_mul (idealHexagonVertex i))

theorem compact_radial_sector_rotated_coordinate (i : Fin 6) (b : Bool) (z : H2) :
    star (idealHexagonVertex i)*(cayley (compactRadialSectorIsometry i b z):ℂ)=
      if b then (cayley z:ℂ) else star (cayley z:ℂ) := by
  change star (idealHexagonVertex i)*(cayley (h2Rotation i
    ((if b then IsometryEquiv.refl H2 else verticalReflectionEquiv) z)):ℂ)=_
  rw [h2Rotation_cayley,←mul_assoc,ideal_hexagon_vertex_star_unit,one_mul]
  cases b
  · exact vertical_reflection_cayley_conjugate z
  · rfl

theorem compact_radial_sector_mem_coordinate_iff (i : Fin 6) (b : Bool) (z : H2) :
    z∈compactRadialSector i b ↔ z∈regularHexagonRegion.interior ∧
      Real.sqrt 3*|(star (idealHexagonVertex i)*(cayley z:ℂ)).im| <
        (star (idealHexagonVertex i)*(cayley z:ℂ)).re ∧
      (if b then 0<(star (idealHexagonVertex i)*(cayley z:ℂ)).im
       else (star (idealHexagonVertex i)*(cayley z:ℂ)).im<0) := by
  have himem (y : H2) : compactRadialSectorIsometry i b y ∈ regularHexagonRegion.interior ↔
      y∈regularHexagonRegion.interior := by
    have hrot (u : H2) : h2RotationIso i u ∈ regularHexagonRegion.interior ↔ u∈regularHexagonRegion.interior := by
      have he := regular_hexagon_rotation_interior i
      constructor
      · intro hu
        rw [←he] at hu
        exact (h2RotationIso i).injective.mem_set_image.mp hu
      · intro hu
        rw [←he]
        exact ⟨u,hu,rfl⟩
    change h2RotationIso i ((if b then IsometryEquiv.refl H2 else verticalReflectionEquiv) y) ∈ _ ↔ _
    rw [hrot]
    cases b
    · exact regular_hexagon_reflection_mem_interior y
    · rfl
  have hmem (y : H2) : y∈compactRadialFirstPiece ↔
      compactRadialSectorIsometry i b y∈regularHexagonRegion.interior ∧
      Real.sqrt 3*|(star (idealHexagonVertex i)*(cayley (compactRadialSectorIsometry i b y):ℂ)).im| <
        (star (idealHexagonVertex i)*(cayley (compactRadialSectorIsometry i b y):ℂ)).re ∧
      (if b then 0<(star (idealHexagonVertex i)*(cayley (compactRadialSectorIsometry i b y):ℂ)).im
       else (star (idealHexagonVertex i)*(cayley (compactRadialSectorIsometry i b y):ℂ)).im<0) := by
    rw [himem,compact_radial_sector_rotated_coordinate]
    change (y∈regularHexagonRegion.interior ∧ 0<(cayley y:ℂ).im ∧
      Real.sqrt 3*(cayley y:ℂ).im<(cayley y:ℂ).re) ↔ _
    cases b <;> simp only [Bool.false_eq_true,ite_false,ite_true,Complex.star_def,Complex.conj_re,Complex.conj_im,neg_lt_zero,abs_neg]
    all_goals constructor
    all_goals rintro ⟨hy,h₁,h₂⟩
    · exact ⟨hy,by simpa only [abs_of_pos h₁] using h₂,h₁⟩
    · exact ⟨hy,h₂,by simpa only [abs_of_pos h₂] using h₁⟩
    · exact ⟨hy,by simpa only [abs_of_pos h₁] using h₂,h₁⟩
    · exact ⟨hy,h₂,by simpa only [abs_of_pos h₂] using h₁⟩
  constructor
  · rintro ⟨y,hy,rfl⟩; exact (hmem y).mp hy
  · intro hz
    refine ⟨(compactRadialSectorIsometry i b).symm z,?_,(compactRadialSectorIsometry i b).apply_symm_apply z⟩
    apply (hmem _).mpr
    simpa only [(compactRadialSectorIsometry i b).apply_symm_apply] using hz

end CurveComplex.Hyperbolic
