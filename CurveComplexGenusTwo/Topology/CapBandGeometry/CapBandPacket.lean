import CurveComplexGenusTwo.Topology.CapBandGeometry.BandCollarRetraction

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

/-- Concrete, unconditional cover geometry for the same square/two-band witness.
The overlap's four pieces and the middle set's two pieces are constructed,
not supplied as new hypotheses to the cap producer. -/
theorem actual_band_homology_cover_geometry
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := bandUnion D B
    closure (interior N) = N ∧
    IsOpen ((Subtype.val : N → S) ⁻¹' squareCollars D B) ∧
    IsOpen ((Subtype.val : N → S) ⁻¹' middleBands B) ∧
    squareCollars D B ∪ middleBands B = N ∧
    ContractibleSpace (squareCollars D B) ∧
    Disjoint (bandSlice B.first (Ioo (1/4 : ℝ) (3/4)))
      (bandSlice B.second (Ioo (1/4 : ℝ) (3/4))) ∧
    ContractibleSpace (bandSlice B.first (Ioo (1/4 : ℝ) (3/4))) ∧
    ContractibleSpace (bandSlice B.second (Ioo (1/4 : ℝ) (3/4))) ∧
    (⋃ i : Fin 4, overlapPiece B i) = squareCollars D B ∩ middleBands B ∧
    Pairwise (fun i j : Fin 4 => Disjoint (overlapPiece B i) (overlapPiece B j)) ∧
    (∀ i : Fin 4, ContractibleSpace (overlapPiece B i)) := by
  obtain ⟨hdisjoint, hfirst, hsecond⟩ := middleBands_components B
  exact ⟨compatibleOutsideBands_regular_closed D B,
    squareCollars_relative_open D B, middleBands_relative_open D B,
    squareCollars_middleBands_cover D B, squareCollars_contractible D B,
    hdisjoint, hfirst, hsecond, overlapPiece_union D B,
    overlapPiece_pairwise_disjoint B, overlapPiece_contractible B⟩

#print axioms actual_band_homology_cover_geometry
end CurveComplex.CapBandGeometry
