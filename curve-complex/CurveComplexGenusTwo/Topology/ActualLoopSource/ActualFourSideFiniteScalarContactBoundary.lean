import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourSideBoundaryFaceValues
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Literal finite contacts on four actual paths construct the compatible
boundary map needed by the actual contact filling producer. -/
theorem actual_four_side_finite_scalar_contact_boundary
    (V : Set (ℝ × ℝ)) {bl br tl tr : V}
    (bottom : Path bl br) (right : Path br tr) (top : Path tl tr) (left : Path bl tl)
    (hbottom : {t : Interval | (bottom t).val.2=0}.Finite)
    (hright : {t : Interval | (right t).val.2=0}.Finite)
    (htop : {t : Interval | (top t).val.2=0}.Finite)
    (hleft : {t : Interval | (left t).val.2=0}.Finite) :
    ∃ f : C({z : ℝ × ℝ // ‖z‖=1},V),
      (∀ i : Fin 4,∀ t,f (actualMaxNormSquareBoundaryFace i t)=
        if i.val=0 then bottom t else if i.val=1 then right t
        else if i.val=2 then top t else left t) ∧
      (∀ i : Fin 4,{t : Interval | (f (actualMaxNormSquareBoundaryFace i t)).val.2=0}.Finite) := by
  obtain ⟨f,hvalues⟩ := actual_four_side_boundary_face_values bottom right top left
  refine ⟨f,hvalues,?_⟩
  intro i
  fin_cases i
  · simpa [hvalues] using hbottom
  · simpa [hvalues] using hright
  · simpa [hvalues] using htop
  · simpa [hvalues] using hleft
end CurveComplex.HyperellipticModel
