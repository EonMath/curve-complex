import CurveComplexGenusTwo.Topology.ActualMain14Dictionary.Providers.Main14ActualMarkedStrictBigon

namespace CurveComplex.BranchedDoubleCover
open Set Topology
set_option maxHeartbeats 4000000

/-- Literal transverse coordinate crossings of whole full preimages descend
through the actual regular projection charts. -/
theorem transverse_full_preimages_descends
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (a b : Curve E) (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image)
    (hfree : Disjoint c.image (q.branch : Set S))
    (ht : Transverse a b) : Transverse c d := by
  classical
  have hset : q.projection '' (a.image ∩ b.image) = c.image ∩ d.image := by
    ext y; constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [ha,hb,Set.mem_preimage,Set.mem_inter_iff] using hx
    · intro hy
      obtain ⟨x,rfl⟩ := q.projection_surjective y
      refine ⟨x,?_,rfl⟩
      simpa only [ha,hb,Set.mem_preimage,Set.mem_inter_iff] using hy
  refine ⟨?_,?_⟩
  · rw [← hset]; exact ht.1.image q.projection
  · intro y hy
    obtain ⟨x,rfl⟩ := q.projection_surjective y
    have hx : x ∈ a.image ∩ b.image := by
      simpa only [ha,hb,Set.mem_preimage,Set.mem_inter_iff] using hy
    have hregular : q.projection x ∈ (q.branch : Set S)ᶜ :=
      fun h => Set.disjoint_left.mp hfree hy.1 h
    obtain ⟨G,hxG,hG⟩ := q.unbranched_cover.isLocalHomeomorphOn x hregular
    obtain ⟨F,hxF,hFU,hF0,hFa,hFb⟩ :=
      source_crossing_open_partial_chart (ht.2 x hx) Set.univ isOpen_univ (Set.mem_univ x)
    let H := G.symm.trans F
    have hGx : G x = q.projection x := (congrFun hG x).symm
    have hyG : q.projection x ∈ G.target := hGx ▸ G.map_source hxG
    have hinv : G.symm (q.projection x) = x := by rw [← hGx]; exact G.left_inv hxG
    have hyH : q.projection x ∈ H.source := by
      change q.projection x ∈ G.target ∩ G.symm ⁻¹' F.source
      exact ⟨hyG,by simpa only [Set.mem_preimage,hinv] using hxF⟩
    have hH0 : H (q.projection x) = (0,0) := by
      change F (G.symm (q.projection x)) = (0,0)
      rw [hinv,hF0]
    refine ⟨H.source,H.target,hyH,H.toHomeomorphSourceTarget,H.open_source,H.open_target,hH0,?_⟩
    intro z hz
    have hzG : z ∈ G.target := hz.1
    have hzF : G.symm z ∈ F.source := hz.2
    have hzGs : G.symm z ∈ G.source := G.map_target hzG
    have hproj : q.projection (G.symm z) = z := (congrFun hG (G.symm z)).trans (G.right_inv hzG)
    have hca : z ∈ c.image ↔ G.symm z ∈ a.image := by
      rw [ha,Set.mem_preimage,hproj]
    have hdb : z ∈ d.image ↔ G.symm z ∈ b.image := by
      rw [hb,Set.mem_preimage,hproj]
    exact ⟨hca.trans (hFa _ hzF),hdb.trans (hFb _ hzF)⟩
end CurveComplex.BranchedDoubleCover
