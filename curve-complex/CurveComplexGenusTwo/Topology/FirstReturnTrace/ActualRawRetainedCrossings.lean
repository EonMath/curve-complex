import CurveComplexGenusTwo.Topology.FirstReturnTrace.ActualCrossingLocalTransfer
namespace CurveComplex
open Set Topology
/-- Every retained crossing of an actual first-return branch is already a
genuine crossing of that WHOLE raw boundary with the target curve. -/
theorem source_raw_branch_retained_crossings
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : SourceFirstReturnBoundary a b)
    (B : SourceTwoSurgeryBranches D) (ht : Transverse a b) (i : Bool) :
    ∀ p ∈ source_surgery_retained_crossings B i, CrossesAt a (B.boundary i) p := by
  obtain ⟨E,hp,hdis,hfirst,hother,ha,hb,hraw⟩ :=
    source_retained_branch_crossing_charts D B ht i
  intro p hpR
  let q : source_surgery_retained_crossings B i := ⟨p,hpR⟩
  refine ⟨(E q).source,(E q).target,(hp q).1,(E q).toHomeomorphSourceTarget,
    (E q).open_source,(E q).open_target,(hp q).2,?_⟩
  intro x hx
  exact ⟨ha q x hx,hraw q x hx⟩
end CurveComplex
#print axioms CurveComplex.source_raw_branch_retained_crossings
