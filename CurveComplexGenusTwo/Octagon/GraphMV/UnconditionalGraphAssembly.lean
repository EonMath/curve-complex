import CurveComplexGenusTwo.Octagon.GraphMV.GraphCertificateRepair
import CurveComplexGenusTwo.Octagon.GraphMV.GraphMVNaturalityAssembly
import CurveComplexGenusTwo.Octagon.GraphMV.EdgeNaturalityProof
import CurveComplexGenusTwo.Octagon.GraphMV.OverlapAugmentationStatements

noncomputable section
open CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
namespace CurveComplex.Octagon

/-- Genuine open existence obligation for the actual four-edge graph H₁ computation.
The proof must assemble the actual overlap and edge coordinate providers. -/
theorem actualBoundaryGraphH1Iso_nonempty :
    Nonempty (H AttachingMap.BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  exact ⟨AttachingMap.GraphMV.graph_H1_iso_of_overlap_edge_data
    AttachingMap.GraphMV.overlapHZeroCoordinates
    AttachingMap.GraphMV.edgeHZeroCoordinates
    AttachingMap.GraphMV.overlap_augmentation_sum
    AttachingMap.GraphMV.edgeInclusion_coordinates⟩

/-- Chosen from the explicit actual-graph existence theorem, with no placeholder data body. -/
def actualBoundaryGraphH1Iso :
    H AttachingMap.BoundaryGraph 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  Classical.choice actualBoundaryGraphH1Iso_nonempty

/-- Integral homology in every degree at least two vanishes for the actual graph. -/
theorem actualBoundaryGraphHigherZero (n : ℕ) (hn : 2 ≤ n) :
    IsZero (H AttachingMap.BoundaryGraph n) := by
  exact AttachingMap.GraphMV.graph_higher_zero_of_overlap
    AttachingMap.GraphMV.overlap_positive_homology n hn

/-- Constructed certificate contains exactly the actual unconditional graph results. -/
def actualBoundaryGraphNumericalCertificate : BoundaryGraphNumericalCertificate where
  h1Iso := actualBoundaryGraphH1Iso
  higherZero := actualBoundaryGraphHigherZero

/-- Actual surface-to-boundary comparison composed with the genuine graph computation. -/
def actualSurfaceH1IsoUnconditional :
    H Surface 1 ≅ ModuleCat.of ℤ (Fin 4 → ℤ) :=
  actualSurfaceH1Iso actualBoundaryGraphNumericalCertificate

theorem actualSurfaceH1FinrankUnconditional :
    Module.finrank ℤ (H Surface 1) = 4 := by
  exact actualSurfaceH1_finrank actualBoundaryGraphNumericalCertificate

/-- The isomorphism retains the actual surface connecting map as its forward morphism. -/
def actualSurfaceH2IsoUnconditional : H Surface 2 ≅ ModuleCat.of ℤ ℤ :=
  actualSurfaceH2Iso actualBoundaryGraphNumericalCertificate

end CurveComplex.Octagon
