import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourLiteralSideBoundary
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The constructed four-side boundary retains every literal original edge
parameter, including all four corners. -/
theorem actual_four_side_boundary_face_values
    {Y : Type} [TopologicalSpace Y] {bl br tl tr : Y}
    (bottom : Path bl br) (right : Path br tr) (top : Path tl tr) (left : Path bl tl) :
    ∃ f : C({z : ℝ × ℝ // ‖z‖=1},Y),
      ∀ i : Fin 4,∀ t,f (actualMaxNormSquareBoundaryFace i t)=
        if i.val=0 then bottom t else if i.val=1 then right t
        else if i.val=2 then top t else left t := by
  obtain ⟨f,hf⟩ := actual_four_literal_side_boundary bottom right top left
  refine ⟨f,?_⟩
  intro i t
  fin_cases i
  · change f (actualMaxNormSquareBoundaryFace 0 t)=bottom t
    have hh := (hf (actualMaxNormSquareBoundaryFace 0 t)).1 (by rfl)
    have hc : (actualNormalizedMaxNormSquare
        ⟨(actualMaxNormSquareBoundaryFace 0 t).val,(actualMaxNormSquareBoundaryFace 0 t).property.le⟩).1=t := by
      apply Subtype.ext
      change ((2*t.val-1)+1)/2=t.val
      ring
    simpa only [hc] using hh
  · change f (actualMaxNormSquareBoundaryFace 1 t)=right t
    have hh := (hf (actualMaxNormSquareBoundaryFace 1 t)).2.1 (by rfl)
    have hc : (actualNormalizedMaxNormSquare
        ⟨(actualMaxNormSquareBoundaryFace 1 t).val,(actualMaxNormSquareBoundaryFace 1 t).property.le⟩).2=t := by
      apply Subtype.ext
      change ((2*t.val-1)+1)/2=t.val
      ring
    simpa only [hc] using hh
  · change f (actualMaxNormSquareBoundaryFace 2 t)=top t
    have hh := (hf (actualMaxNormSquareBoundaryFace 2 t)).2.2.1 (by rfl)
    have hc : (actualNormalizedMaxNormSquare
        ⟨(actualMaxNormSquareBoundaryFace 2 t).val,(actualMaxNormSquareBoundaryFace 2 t).property.le⟩).1=t := by
      apply Subtype.ext
      change ((2*t.val-1)+1)/2=t.val
      ring
    simpa only [hc] using hh
  · change f (actualMaxNormSquareBoundaryFace 3 t)=left t
    have hh := (hf (actualMaxNormSquareBoundaryFace 3 t)).2.2.2 (by rfl)
    have hc : (actualNormalizedMaxNormSquare
        ⟨(actualMaxNormSquareBoundaryFace 3 t).val,(actualMaxNormSquareBoundaryFace 3 t).property.le⟩).2=t := by
      apply Subtype.ext
      change ((2*t.val-1)+1)/2=t.val
      ring
    simpa only [hc] using hh
end CurveComplex.HyperellipticModel
