import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopAllowedOriginalFirstContactBoundary
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSameClassMarkedSweep
namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Literal original same-class loops have the same marked basepoint. -/
theorem actual_same_class_loop_literal_base
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b) :
    a.val.map 0=b.val.map 0 := by
  obtain ⟨F,_,_,he,_,hi⟩ := actual_same_class_marked_arc_sweep M b a hclass.symm
  have hm : F (1,0) ∈ a.val.image := by rw [← hi]; exact mem_range_self 0
  obtain ⟨t,ht⟩ := hm
  have hmark : a.val.map t ∈ (M.cover.branch : Set S) := ht ▸ ((he 1).1 ▸ b.val.start_marked)
  rcases a.val.marked_only_at_ends t hmark with rfl | rfl
  · exact ht.trans (he 1).1
  · exact ha.trans (ht.trans (he 1).1)

/-- Original same-class loops produce a genuine two-original-side Jordan
candidate at positive mutual crossing. Empty-side SELECTION is not asserted. -/
theorem actual_same_class_loop_original_first_contact_boundary
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1)
    (hclass : Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b)
    (hfinite : (ArcSurgery.crossings M a b).Finite)
    (p : S) (hp : p ∈ ArcSurgery.crossings M a b) :
    ∃ (f g : C(Interval,S)) (v : S) (c : Curve S),
      IsEmbedding f ∧ IsEmbedding g ∧
      range f ⊆ a.val.image ∧ range g ⊆ b.val.image ∧
      f 0=b.val.map 0 ∧ g 0=b.val.map 0 ∧ f 1=v ∧ g 1=v ∧
      b.val.map 0≠v ∧ v ∈ ArcSurgery.crossings M a b ∧
      range f ∩ range g={b.val.map 0,v} ∧ c.image=range f ∪ range g := by
  exact actual_loop_allowed_shared_start_first_contact_jordan_boundary M a b
    (actual_same_class_loop_literal_base M a b ha hclass) hfinite p hp
end CurveComplex.HyperellipticModel
