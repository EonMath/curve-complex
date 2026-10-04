import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassMarkedSweep
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Literal same-class source isotopy retains whether its marked trace is a loop. -/
theorem actual_same_class_loop_closure_invariant
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    (a.val.map 0=a.val.map 1) ↔ (b.val.map 0=b.val.map 1) := by
  have transfer (c d : EssentialMarkedArc M)
      (hc : Quotient.mk (essentialArcSetoid M) c = Quotient.mk (essentialArcSetoid M) d)
      (hd : d.val.map 0=d.val.map 1) : c.val.map 0=c.val.map 1 := by
    obtain ⟨F,_,_,he,_,hi⟩ := actual_same_class_marked_arc_sweep M c d hc
    have hbase (t : Interval) (hm : F (1,t) ∈ (M.cover.branch : Set S)) : F (1,t)=d.val.map 0 := by
      have hmem : F (1,t) ∈ d.val.image := by rw [← hi]; exact mem_range_self t
      obtain ⟨s,hs⟩ := hmem
      rcases d.val.marked_only_at_ends s (hs ▸ hm) with rfl | rfl
      · exact hs.symm
      · exact hs.symm.trans hd.symm
    exact (he 1).1.symm.trans ((hbase 0 ((he 1).1 ▸ c.val.start_marked)).trans
      ((hbase 1 ((he 1).2 ▸ c.val.end_marked)).symm.trans (he 1).2))
  exact ⟨transfer b a hclass.symm,transfer a b hclass⟩
end CurveComplex.HyperellipticModel
