import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPositiveNormalPoleSigns
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSelectedCellFourEdgeCoordinates
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- On a literal original boundary side, any produced selected-cell coordinate
has exactly the supplied source normal. Equality follows from the original BC
embedding, even at face endpoints. -/
theorem actual_literal_cell_boundary_source_normal
    {S : Type} [TopologicalSpace S]
    (BC : Interval × Icc (-1:ℝ) 1 → S) (hBC : IsEmbedding BC)
    (final : C(Interval × Interval,S))
    (coordinate : C(Interval × Interval,Interval × Icc (-1:ℝ) 1))
    (hdecode : ∀ z,BC (coordinate z)=final z)
    (i : Fin 4) (source : C(Interval,S))
    (hliteral : ∀ t,final (actualLiteralCellSide i t)=source t)
    (T : Set Interval) (Q : C(T,range BC))
    (hQ : ∀ t : T,(Q t).val=source t.val)
    (normal : C(T,ℝ))
    (hnormal : ∀ t : T,normal t=((hBC.toHomeomorph.symm (Q t)).2:ℝ)) :
    ∀ t : T,(coordinate (actualLiteralCellSide i t.val)).2.val=normal t := by
  intro t
  have hq : BC (hBC.toHomeomorph.symm (Q t))=source t.val :=
    (congrArg Subtype.val (hBC.toHomeomorph.apply_symm_apply (Q t))).trans (hQ t)
  have he : coordinate (actualLiteralCellSide i t.val)=hBC.toHomeomorph.symm (Q t) :=
    hBC.injective ((hdecode _).trans ((hliteral t.val).trans hq.symm))
  rw [he]
  exact (hnormal t).symm
end CurveComplex.HyperellipticModel
