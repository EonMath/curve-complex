import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourPathCellContactDegreeFamily
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellFourEdgeCoordinates
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual four literal cell sides are exactly the normalized max-norm
boundary faces, including all original corners. -/
theorem actual_normalized_square_literal_faces (i : Fin 4) (t : Interval) :
    actualNormalizedMaxNormSquare.symm (actualLiteralCellSide i t)=
      ⟨(actualMaxNormSquareBoundaryFace i t).val,
        (actualMaxNormSquareBoundaryFace i t).property.le⟩ := by
  apply Subtype.ext
  fin_cases i
  · change (2*t.val-1,2*(0:ℝ)-1)=(2*t.val-1,-1)
    norm_num
  · change (2*(1:ℝ)-1,2*t.val-1)=(1,2*t.val-1)
    norm_num
  · change (2*t.val-1,2*(1:ℝ)-1)=(2*t.val-1,1)
    norm_num
  · change (2*(0:ℝ)-1,2*t.val-1)=(-1,2*t.val-1)
    norm_num
end CurveComplex.HyperellipticModel
