import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualFourEdgeJointBoundaryMovie
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualParameterizedBoundarySquareExtension
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Four actual compatible edge movies extend jointly through the convex cell.
The extension is constructed from those movies, rather than supplied as data. -/
theorem actual_four_edge_joint_convex_cell_extension
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V) (bl br tl tr : V)
    (bottom right top left : C(Interval × Interval,V))
    (hb : ∀ σ, bottom (σ,0)=bl ∧ bottom (σ,1)=br)
    (hr : ∀ σ, right (σ,0)=br ∧ right (σ,1)=tr)
    (ht : ∀ σ, top (σ,0)=tl ∧ top (σ,1)=tr)
    (hl : ∀ σ, left (σ,0)=bl ∧ left (σ,1)=tl)
    (v : C(Interval,V)) :
    ∃ H : C((Interval × Interval) × Interval,V),
      ∀ σ t, H ((t,0),σ)=bottom (σ,t) ∧
        H ((1,t),σ)=right (σ,t) ∧ H ((t,1),σ)=top (σ,t) ∧
        H ((0,t),σ)=left (σ,t) := by
  obtain ⟨f,hf⟩ := actual_four_edge_joint_boundary_movie bl br tl tr
    bottom right top left hb hr ht hl
  obtain ⟨H,hH⟩ := actual_parameterized_boundary_square_extension V hV f v
  have hs (i : Fin 4) (t : Interval) :
      actualNormalizedMaxNormSquare
        ⟨(actualMaxNormSquareBoundaryFace i t).val,
          (actualMaxNormSquareBoundaryFace i t).property.le⟩ =
        if i.val=0 then (t,0) else if i.val=1 then (1,t)
        else if i.val=2 then (t,1) else (0,t) := by
    fin_cases i <;> apply Prod.ext <;> apply Subtype.ext <;>
      simp [actualNormalizedMaxNormSquare,
        actualMaxNormSquareBoundaryFace]
  refine ⟨H,?_⟩
  intro σ t
  have hh (i : Fin 4) := hH σ (actualMaxNormSquareBoundaryFace i t)
  have hv (i : Fin 4) := hf σ i t
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [hs,Fin.val_zero,ite_true] using (hh 0).trans (hv 0)
  · simpa [hs] using (hh 1).trans (hv 1)
  · simpa [hs] using (hh 2).trans (hv 2)
  · simpa [hs] using (hh 3).trans (hv 3)
end CurveComplex.HyperellipticModel
