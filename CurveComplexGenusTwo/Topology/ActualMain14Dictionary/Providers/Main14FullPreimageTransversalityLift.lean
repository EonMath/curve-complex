import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14Circle33FiniteBigonElimination

namespace CurveComplex.BranchedDoubleCover
open Set Topology
set_option maxHeartbeats 4000000

/-- Actual finite two-point fibers and regular projection charts lift a
transverse downstairs circle pair to their literal whole full preimages. -/
theorem transverse_full_preimages_lifts
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (a b : Curve E) (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image)
    (hfree : Disjoint c.image (q.branch : Set S))
    (ht : Transverse c d) : Transverse a b := by
  classical
  let lift : S → E := fun y => Classical.choose (q.projection_surjective y)
  have hlift (y : S) : q.projection (lift y) = y := Classical.choose_spec (q.projection_surjective y)
  have hsubset : a.image ∩ b.image ⊆
      lift '' (c.image ∩ d.image) ∪ q.deck '' (lift '' (c.image ∩ d.image)) := by
    intro x hx
    have hy : q.projection x ∈ c.image ∩ d.image := by
      simpa only [ha,hb,Set.mem_preimage,Set.mem_inter_iff] using hx
    have hp : q.projection (lift (q.projection x)) = q.projection x := hlift _
    rcases (q.fiber_pair _ _).mp hp with hh | hh
    · exact Or.inl ⟨q.projection x,hy,hh.symm⟩
    · exact Or.inr ⟨lift (q.projection x),⟨q.projection x,hy,rfl⟩,hh.symm⟩
  refine ⟨((ht.1.image lift).union ((ht.1.image lift).image q.deck)).subset hsubset,?_⟩
  intro x hx
  have hy : q.projection x ∈ c.image ∩ d.image := by
    simpa only [ha,hb,Set.mem_preimage,Set.mem_inter_iff] using hx
  have hregular : q.projection x ∈ (q.branch : Set S)ᶜ :=
    fun h => Set.disjoint_left.mp hfree hy.1 h
  obtain ⟨G,hxG,hG⟩ := q.unbranched_cover.isLocalHomeomorphOn x hregular
  obtain ⟨F,hyF,hFU,hF0,hFc,hFd⟩ :=
    source_crossing_open_partial_chart (ht.2 _ hy) Set.univ isOpen_univ (Set.mem_univ _)
  let H := G.trans F
  have hGx : G x = q.projection x := (congrFun hG x).symm
  have hxH : x ∈ H.source := by
    change x ∈ G.source ∩ G ⁻¹' F.source
    refine ⟨hxG,?_⟩
    change G x ∈ F.source
    rw [hGx]
    exact hyF
  have hH0 : H x = (0,0) := by
    change F (G x) = (0,0)
    rw [hGx,hF0]
  refine ⟨H.source,H.target,hxH,H.toHomeomorphSourceTarget,H.open_source,H.open_target,hH0,?_⟩
  intro z hz
  have hzF : G z ∈ F.source := hz.2
  have hca : z ∈ a.image ↔ G z ∈ c.image := by rw [ha,Set.mem_preimage,congrFun hG z]
  have hdb : z ∈ b.image ↔ G z ∈ d.image := by rw [hb,Set.mem_preimage,congrFun hG z]
  exact ⟨hca.trans (hFc _ hzF),hdb.trans (hFd _ hzF)⟩
end CurveComplex.BranchedDoubleCover
