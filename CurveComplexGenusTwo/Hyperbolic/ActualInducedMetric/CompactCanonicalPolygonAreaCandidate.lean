import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.CompactTwelveSectorDecompositionCandidate

namespace CurveComplex.Hyperbolic
open Set MeasureTheory
open scoped MeasureTheory NNReal ENNReal

theorem regular_hexagon_normalized_interior_area :
    (μHE[2] : Measure H2) regularHexagonRegion.interior=ENNReal.ofReal Real.pi := by
  have he : (μHE[2] : Measure H2) regularHexagonRegion.interior =
      (μHE[2] : Measure H2) (⋃p : Fin 6 × Bool,compactRadialSector p.1 p.2) := by
    apply le_antisymm
    · calc
        _ ≤ (μHE[2] : Measure H2) ((⋃p : Fin 6 × Bool,compactRadialSector p.1 p.2) ∪ compactRadialExceptional) :=
          measure_mono compact_radial_sectors_cover_mod_exceptional
        _ ≤ (μHE[2] : Measure H2) (⋃p : Fin 6 × Bool,compactRadialSector p.1 p.2) +
            (μHE[2] : Measure H2) compactRadialExceptional := measure_union_le _ _
        _ = _ := by rw [compact_radial_exceptional_normalized_area_zero,add_zero]
    · exact measure_mono compact_radial_sectors_union_subset
  rw [he,measure_iUnion compact_radial_sectors_pairwise_disjoint
    (fun p => (compact_radial_sector_isOpen p.1 p.2).measurableSet)]
  simp_rw [compact_radial_sector_area]
  rw [tsum_fintype]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  norm_num only [Nat.reduceMul]
  rw [nsmul_eq_mul]
  norm_num only [Nat.cast_ofNat]
  have h : (12 : ℝ≥0∞)=ENNReal.ofReal (12 : ℝ) := by norm_num
  rw [h,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤12)]
  congr 1
  ring

end CurveComplex.Hyperbolic
