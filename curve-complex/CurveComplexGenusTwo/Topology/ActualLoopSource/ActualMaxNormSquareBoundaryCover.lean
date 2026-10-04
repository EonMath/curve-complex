import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMaxNormSquareBoundaryFaces
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual four affine sides cover the full max-norm square boundary. -/
theorem actual_max_norm_square_boundary_cover
    (z : {z : ℝ × ℝ // ‖z‖=1}) :
    ∃ i : Fin 4,∃ t : Interval,actualMaxNormSquareBoundaryFace i t=z := by
  have hb : |z.val.1|≤1 ∧ |z.val.2|≤1 := by
    have h : max |z.val.1| |z.val.2|=1 := by
      simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
    exact ⟨(le_max_left _ _).trans h.le,(le_max_right _ _).trans h.le⟩
  have hw : |z.val.1|=1 ∨ |z.val.2|=1 := by
    have h : max |z.val.1| |z.val.2|=1 := by
      simpa only [Prod.norm_def,Real.norm_eq_abs] using z.property
    rw [max_def] at h
    split_ifs at h with he
    · exact Or.inr h
    · exact Or.inl h
  let tx : Interval := ⟨(z.val.1+1)/2,by
    have h := abs_le.mp hb.1
    constructor <;> linarith only [h.1,h.2]⟩
  let ty : Interval := ⟨(z.val.2+1)/2,by
    have h := abs_le.mp hb.2
    constructor <;> linarith only [h.1,h.2]⟩
  rcases hw with hx | hy
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hx with hx | hx
    · refine ⟨1,ty,?_⟩
      apply Subtype.ext
      change (1,2*((z.val.2+1)/2)-1)=z.val
      apply Prod.ext
      · exact hx.symm
      · ring
    · refine ⟨3,ty,?_⟩
      apply Subtype.ext
      change (-1,2*((z.val.2+1)/2)-1)=z.val
      apply Prod.ext
      · exact hx.symm
      · ring
  · rcases (abs_eq (by norm_num : (0:ℝ)≤1)).mp hy with hy | hy
    · refine ⟨2,tx,?_⟩
      apply Subtype.ext
      change (2*((z.val.1+1)/2)-1,1)=z.val
      apply Prod.ext
      · ring
      · exact hy.symm
    · refine ⟨0,tx,?_⟩
      apply Subtype.ext
      change (2*((z.val.1+1)/2)-1,-1)=z.val
      apply Prod.ext
      · ring
      · exact hy.symm
end CurveComplex.HyperellipticModel
