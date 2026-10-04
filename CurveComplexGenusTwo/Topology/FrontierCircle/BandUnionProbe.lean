import CurveComplexGenusTwo.Topology.FrontierCircle.GlobalBandScaffold

open Set Topology unitInterval
namespace CurveComplex

/-- Compactness, connectedness and coverage use the actual shared square/bands. -/
theorem compatibleOutsideBands_compact_connected_cover_probe
    {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    IsCompact N ∧ IsConnected N ∧ a.image ∪ b.image ⊆ N := by
  haveI : Fact ((-1:ℝ) ≤ 1) := ⟨by norm_num⟩
  haveI : ConnectedSpace (Metric.closedBall ((0,0):ℝ×ℝ) D.radius) :=
    (isConnected_iff_connectedSpace.mp (Metric.isConnected_closedBall D.radius_pos.le))
  haveI : ConnectedSpace BandWidth :=
    isConnected_iff_connectedSpace.mp (isConnected_Icc (show (-1:ℝ) ≤ 1 by norm_num))
  have hD := isConnected_range D.square_embedded.continuous
  have hB := isConnected_range B.first_embedded.continuous
  have hC := isConnected_range B.second_embedded.continuous
  have hmeet : (Set.range D.square ∩ Set.range B.first).Nonempty := by
    refine ⟨B.first (0,⟨0,by norm_num⟩),?_,Set.mem_range_self _⟩
    rw [B.first_bottom]
    exact Set.mem_range_self _
  have hmeet' : ((Set.range D.square ∪ Set.range B.first) ∩ Set.range B.second).Nonempty := by
    refine ⟨B.second (0,⟨0,by norm_num⟩),Or.inl ?_,Set.mem_range_self _⟩
    rw [B.second_left]
    exact Set.mem_range_self _
  refine ⟨((isCompact_range D.square_embedded.continuous).union
    (isCompact_range B.first_embedded.continuous)).union
    (isCompact_range B.second_embedded.continuous),
    (hD.union hmeet hB).union hmeet' hC,?_⟩
  intro z hz
  by_cases hO : z ∈ D.openSquare
  · left; left
    rw [D.openSquare_eq] at hO
    exact Set.image_subset_range _ _ hO
  · rcases hz with ha | hb
    · left; right
      have hp : z ∈ Set.range D.firstArc := D.firstArc_range ▸ ⟨ha,hO⟩
      obtain ⟨t,rfl⟩ := hp
      exact ⟨(t,⟨0,by norm_num⟩),B.first_center t⟩
    · right
      have hp : z ∈ Set.range D.secondArc := D.secondArc_range ▸ ⟨hb,hO⟩
      obtain ⟨t,rfl⟩ := hp
      exact ⟨(t,⟨0,by norm_num⟩),B.second_center t⟩

#print axioms compatibleOutsideBands_compact_connected_cover_probe
end CurveComplex
