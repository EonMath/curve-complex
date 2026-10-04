import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalHorizontalBandGraphClosure
open Set Topology Schoenflies CurveComplex
/-- On the closed torus a literal horizontal reference has an actual ambient
translation to the zero-height winding reference. -/
theorem actual_horizontal_reference_has_zero_height_isotopy (h : ℝ) :
    ∃ H : AmbientIsotopy (Circle×Circle),
      H.finalMap '' range (fun z : Circle => (z,Circle.exp h))=
        range (fun z : Circle => (z,1)) := by
  let H : AmbientIsotopy (Circle×Circle) := {
    map := ⟨fun z => (z.2.1,Circle.exp (-(z.1:ℝ)*h)*z.2.2),by fun_prop⟩
    homeomorphism_at := by
      intro t
      exact ⟨(Homeomorph.refl Circle).prodCongr
        (Homeomorph.mulLeft (Circle.exp (-(t:ℝ)*h))),fun _ => rfl⟩
    at_zero := by intro z; simp }
  refine ⟨H,?_⟩
  have hfinal (z : Circle) : H.finalMap (z,Circle.exp h)=(z,1) := by
    change (z,Circle.exp (-(1:ℝ)*h)*Circle.exp h)=(z,1)
    rw [← Circle.exp_add]
    simp
  ext z
  constructor
  · rintro ⟨_,⟨w,rfl⟩,rfl⟩
    exact ⟨w,(hfinal w).symm⟩
  · rintro ⟨w,rfl⟩
    exact ⟨(w,Circle.exp h),mem_range_self w,hfinal w⟩
#print axioms actual_horizontal_reference_has_zero_height_isotopy
