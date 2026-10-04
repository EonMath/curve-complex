import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactRadialExceptionalCandidate
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactSixRootWedgeCoverProof

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem compact_radial_sectors_pairwise_disjoint :
    Pairwise (fun p q : Fin 6 × Bool => Disjoint (compactRadialSector p.1 p.2) (compactRadialSector q.1 q.2)) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ hne
  apply Set.disjoint_left.mpr
  intro z hzi hzj
  obtain ⟨_,hi,hb⟩ := (compact_radial_sector_mem_coordinate_iff i b z).mp hzi
  obtain ⟨_,hj,hc⟩ := (compact_radial_sector_mem_coordinate_iff j c z).mp hzj
  have hij := six_root_open_wedge_unique (cayley z:ℂ) i j hi hj
  subst j
  cases b <;> cases c <;> simp only [ite_true,ite_false,Bool.false_eq_true] at hb hc
  · exact hne rfl
  · linarith
  · linarith
  · exact hne rfl

theorem compact_radial_sectors_cover_mod_exceptional :
    regularHexagonRegion.interior ⊆ (⋃p : Fin 6 × Bool, compactRadialSector p.1 p.2) ∪ compactRadialExceptional := by
  intro z hz
  by_cases hex : z∈compactRadialExceptional
  · exact Or.inr hex
  · have hn : ¬∃i : Fin 6, (star (idealHexagonVertex i)*(cayley z:ℂ)).im=0 ∨
        (star (idealHexagonVertex i)*(cayley z:ℂ)).re=
          Real.sqrt 3*|(star (idealHexagonVertex i)*(cayley z:ℂ)).im| := by
      intro h; exact hex ((compact_radial_exceptional_mem_iff z).mpr h)
    have hi₀ : ∀i : Fin 6, (star (idealHexagonVertex i)*(cayley z:ℂ)).im≠0 := by
      intro i h; exact hn ⟨i,Or.inl h⟩
    have hb₀ : ∀i : Fin 6, (star (idealHexagonVertex i)*(cayley z:ℂ)).re≠
        Real.sqrt 3*|(star (idealHexagonVertex i)*(cayley z:ℂ)).im| := by
      intro i h; exact hn ⟨i,Or.inr h⟩
    obtain ⟨i,hi⟩ := six_root_open_half_wedge_cover (cayley z:ℂ) hi₀ hb₀
    apply Or.inl
    by_cases hy : 0<(star (idealHexagonVertex i)*(cayley z:ℂ)).im
    · exact mem_iUnion.mpr ⟨(i,true),(compact_radial_sector_mem_coordinate_iff i true z).mpr ⟨hz,hi,hy⟩⟩
    · have hneg : (star (idealHexagonVertex i)*(cayley z:ℂ)).im<0 := lt_of_le_of_ne (le_of_not_gt hy) (hi₀ i)
      exact mem_iUnion.mpr ⟨(i,false),(compact_radial_sector_mem_coordinate_iff i false z).mpr ⟨hz,hi,hneg⟩⟩

theorem compact_radial_sectors_union_subset :
    (⋃p : Fin 6 × Bool, compactRadialSector p.1 p.2) ⊆ regularHexagonRegion.interior := by
  intro z hz
  obtain ⟨p,hp⟩ := mem_iUnion.mp hz
  exact compact_radial_sector_is_subset p.1 p.2 hp

end CurveComplex.Hyperbolic
