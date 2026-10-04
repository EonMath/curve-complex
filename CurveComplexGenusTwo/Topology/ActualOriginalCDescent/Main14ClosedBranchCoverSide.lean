import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14CleanBranchCoverSide
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14ClosedSideWinding

namespace CurveComplex.BranchedDoubleCover

theorem embedded_lifted_interval_closed_projection_covers_circle
    {E S : Type} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) (c : Curve S)
    (hc : Disjoint c.image (q.branch : Set S))
    (α : C(Interval,E)) (hα : Topology.IsEmbedding α)
    (hαc : Set.range α ⊆ q.projection ⁻¹' c.image)
    (hclosed : q.projection (α 0) = q.projection (α 1)) :
    Set.range (q.projection ∘ α) = c.image := by
  let a := q.unramifiedBaseCurve c hc
  have hfree (t : Interval) : q.projection (α t) ∉ q.branch :=
    Set.disjoint_left.mp hc (hαc ⟨t,rfl⟩)
  let A : C(Interval,q.unramifiedTotal) :=
    ⟨fun t => ⟨α t,hfree t⟩,α.continuous.subtype_mk _⟩
  have hA : Topology.IsEmbedding A := Topology.IsEmbedding.subtypeVal.of_comp_iff.mp hα
  have hAa : Set.range A ⊆ q.unramifiedProjection ⁻¹' a.image := by
    rintro z ⟨t,rfl⟩
    exact (q.mem_unramifiedBaseCurve_image c hc _).mpr (hαc ⟨t,rfl⟩)
  have hclosed' : q.unramifiedProjection (A 0) = q.unramifiedProjection (A 1) :=
    Subtype.ext hclosed
  have hsurj := LocalSurgery.embedded_lifted_interval_closed_projection_covers_circle
    q.unramifiedProjection q.unramified_isCoveringMap a A hA hAa hclosed'
  apply Set.Subset.antisymm
  · rintro z ⟨t,rfl⟩
    exact hαc ⟨t,rfl⟩
  · intro z hz
    let zz : q.unramifiedBase := ⟨z,Set.disjoint_left.mp hc hz⟩
    have hzz : zz ∈ a.image := (q.mem_unramifiedBaseCurve_image c hc _).mpr hz
    obtain ⟨t,ht⟩ := hsurj.symm ▸ hzz
    exact ⟨t,congrArg Subtype.val ht⟩

end CurveComplex.BranchedDoubleCover
