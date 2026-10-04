import ChartContracts
import RotationContracts

namespace AlternatingSphereCover
-- Exact approved all-branch endpoint; helper imports await their own review/proof installation.
theorem exists_squareBranchChart (x : Total) (hx : branch (projection x)) :
    Nonempty (CurveComplex.SquareBranchChart Total Sphere projection x) := by
  classical
  have hcomm (z : Total) : projection (totalRotation.symm z)=sphereRotation.symm (projection z) := by
    apply sphereRotation.injective
    rw [sphereRotation.apply_symm_apply,←totalRotation_projection,totalRotation.apply_symm_apply]
  have transfer (z : Total)
      (c : CurveComplex.SquareBranchChart Total Sphere projection (totalRotation.symm z)) :
      Nonempty (CurveComplex.SquareBranchChart Total Sphere projection z) := by
    let up := totalRotation.symm.toOpenPartialHomeomorph.trans c.upstairs
    let down := sphereRotation.symm.toOpenPartialHomeomorph.trans c.downstairs
    refine ⟨{
      upstairs := up
      downstairs := down
      upstairs_mem := ?_
      downstairs_mem := ?_
      upstairs_center := ?_
      downstairs_center := ?_
      image_mem := ?_
      square := ?_ }⟩
    · simpa [up,OpenPartialHomeomorph.trans_source] using c.upstairs_mem
    · simpa [down,OpenPartialHomeomorph.trans_source,←hcomm] using c.downstairs_mem
    · exact c.upstairs_center
    · change c.downstairs (sphereRotation.symm (projection z))=0
      rw [←hcomm]
      exact c.downstairs_center
    · intro y hy
      have hy' : totalRotation.symm y ∈ c.upstairs.source := by
        simpa [up,OpenPartialHomeomorph.trans_source] using hy
      simpa [down,OpenPartialHomeomorph.trans_source,←hcomm] using
        c.image_mem (totalRotation.symm y) hy'
    · intro y hy
      have hy' : totalRotation.symm y ∈ c.upstairs.source := by
        simpa [up,OpenPartialHomeomorph.trans_source] using hy
      change c.downstairs (sphereRotation.symm (projection y))=
        (c.upstairs (totalRotation.symm y))^2
      rw [←hcomm]
      exact c.square (totalRotation.symm y) hy'
  let P : Fin 6 → Prop := fun i => ∀ z : Total, projection z=branchPoint i →
    Nonempty (CurveComplex.SquareBranchChart Total Sphere projection z)
  have hstep (i : Fin 6) (h : P i) : P (nextBranch i) := by
    intro z hz
    apply transfer z
    apply Classical.choice (h (totalRotation.symm z) ?_)
    rw [hcomm,hz,←sphereRotation_branchPoint,sphereRotation.symm_apply_apply]
  have h0 : P 0 := squareBranchChart_at_first
  have h2 : P 2 := hstep 0 h0
  have h4 : P 4 := hstep 2 h2
  have h1 : P 1 := hstep 4 h4
  have h5 : P 5 := hstep 1 h1
  have h3 : P 3 := hstep 5 h5
  obtain ⟨i,hi⟩ := (branch_iff_mem_range (projection x)).mp hx
  fin_cases i
  · exact h0 x hi.symm
  · exact h1 x hi.symm
  · exact h2 x hi.symm
  · exact h3 x hi.symm
  · exact h4 x hi.symm
  · exact h5 x hi.symm
end AlternatingSphereCover
