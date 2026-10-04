import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualMarkedEmptyBigonCleanSides
import CurveComplexGenusTwo.Topology.WeightedSurgery.MarkedArcReverse
namespace CurveComplex.HyperellipticModel
open Set Topology ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
private theorem actualMarkedPointOnOriginalTraceIsPhysicalEndpoint
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M) (x : S)
    (hx : x∈M.cover.branch) (ha : x∈a.val.image) :
    x=a.val.map 0 ∨ x=a.val.map 1 := by
  obtain ⟨t,ht⟩ := ha
  rcases a.val.marked_only_at_ends t (ht ▸ hx) with h | h
  · exact Or.inl (ht.symm.trans (congrArg a.val.map h))
  · exact Or.inr (ht.symm.trans (congrArg a.val.map h))
private theorem actualOriginalLoopContactIsCommonPhysicalBase
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) (hb : b.val.map 0=b.val.map 1)
    (hnot : ¬ (∀ c : Interval,c=0 ∨ c=1 → b.val.map c∉a.val.image)) :
    b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 0 := by
  classical
  push_neg at hnot
  obtain ⟨c,hc,himage⟩ := hnot
  have hmarked : b.val.map c∈M.cover.branch := by
    rcases hc with rfl | rfl
    · exact b.val.start_marked
    · exact b.val.end_marked
  have he : b.val.map c=a.val.map 0 := by
    rcases actualMarkedPointOnOriginalTraceIsPhysicalEndpoint M a _ hmarked himage with h | h
    · exact h
    · exact h.trans ha.symm
  have hbzero : b.val.map c=b.val.map 0 := by
    rcases hc with rfl | rfl
    · rfl
    · exact hb.symm
  exact ⟨hbzero.symm.trans he,hb.symm.trans (hbzero.symm.trans he)⟩
private theorem actualOriginalLoopNonloopContactOrientation
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) (hb : b.val.map 0≠b.val.map 1)
    (hnot : ¬ (∀ c : Interval,c=0 ∨ c=1 → b.val.map c∉a.val.image)) :
    (b.val.map 0=a.val.map 0 ∧ b.val.map 1∉a.val.image) ∨
    (b.val.map 1=a.val.map 0 ∧ b.val.map 0∉a.val.image) := by
  classical
  have endpoint (c : Interval) (hc : c=0 ∨ c=1) (hi : b.val.map c∈a.val.image) :
      b.val.map c=a.val.map 0 := by
    have hm : b.val.map c∈M.cover.branch := by
      rcases hc with rfl | rfl
      · exact b.val.start_marked
      · exact b.val.end_marked
    rcases actualMarkedPointOnOriginalTraceIsPhysicalEndpoint M a _ hm hi with h | h
    · exact h
    · exact h.trans ha.symm
  by_cases h0 : b.val.map 0∈a.val.image
  · have he := endpoint 0 (Or.inl rfl) h0
    refine Or.inl ⟨he,?_⟩
    intro h1
    exact hb (he.trans (endpoint 1 (Or.inr rfl) h1).symm)
  · refine Or.inr ⟨?_,h0⟩
    push_neg at hnot
    obtain ⟨c,hc,hi⟩ := hnot
    rcases hc with rfl | rfl
    · exact False.elim (h0 hi)
    · exact endpoint 1 (Or.inr rfl) hi
private theorem actualOriginalEqualEndpointSetsGiveOrientation
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0≠a.val.map 1)
    (he : classEndpoints M (vertex M a)=classEndpoints M (vertex M b)) :
    (b.val.map 0=a.val.map 0 ∧ b.val.map 1=a.val.map 1) ∨
    (b.val.map 1=a.val.map 0 ∧ b.val.map 0=a.val.map 1) := by
  classical
  change ({a.val.map 0,a.val.map 1}:Finset S)=({b.val.map 0,b.val.map 1}:Finset S) at he
  have hb0 : b.val.map 0=a.val.map 0 ∨ b.val.map 0=a.val.map 1 := by
    have h : b.val.map 0∈({a.val.map 0,a.val.map 1}:Finset S) := he.symm ▸ by simp
    simpa using h
  have hb1 : b.val.map 1=a.val.map 0 ∨ b.val.map 1=a.val.map 1 := by
    have h : b.val.map 1∈({a.val.map 0,a.val.map 1}:Finset S) := he.symm ▸ by simp
    simpa using h
  have ha0 : a.val.map 0=b.val.map 0 ∨ a.val.map 0=b.val.map 1 := by
    have h : a.val.map 0∈({b.val.map 0,b.val.map 1}:Finset S) := he ▸ by simp
    simpa using h
  have ha1 : a.val.map 1=b.val.map 0 ∨ a.val.map 1=b.val.map 1 := by
    have h : a.val.map 1∈({b.val.map 0,b.val.map 1}:Finset S) := he ▸ by simp
    simpa using h
  rcases hb0 with h0 | h0
  · rcases ha1 with h1 | h1
    · exact False.elim (ha (h0.symm.trans h1.symm))
    · exact Or.inl ⟨h0,h1.symm⟩
  · rcases ha0 with h1 | h1
    · exact False.elim (ha (h1.trans h0))
    · exact Or.inr ⟨h1.symm,h0⟩
end CurveComplex.HyperellipticModel
