import CurveComplexGenusTwo.Topology.ActualMain14CoreCut.Main14ActualOriginalBoundaryCollarsLocal

namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace Schoenflies.Plane E]

-- Both original boundary components are the ACTUAL ambient frontier, also after arbitrary endpoint transport.
example (M : HyperellipticModel E S) (a : NonLoopArc M) (N : ArcNeighborhood a)
    (h : E ≃ₜ E)
    (T : Circle × Interval ≃ₜ h '' (M.cover.projection ⁻¹' N.closedSet))
    (hTb : Set.range (fun z : Circle => (T (z,0)).val) ∪
      Set.range (fun z : Circle => (T (z,1)).val) =
      h '' (M.cover.projection ⁻¹' N.boundary.image)) :
    Set.range (fun z : Circle => (T (z,0)).val) ∪
      Set.range (fun z : Circle => (T (z,1)).val) =
      frontier (h '' (M.cover.projection ⁻¹' N.closedSet)) := by
  audit_main14_base3
    letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
    letI : T2Space S := M.sphere.symm.t2Space
    have hopen : IsOpenMap M.cover.projection := by
      have hcl : IsClosedMap M.cover.projection := M.cover.projection_continuous.isClosedMap
      have hq := hcl.isQuotientMap M.cover.projection_continuous M.cover.projection_surjective
      intro U hU
      rw [← hq.isCoinducing.isOpen_preimage]
      have heq : M.cover.projection ⁻¹' (M.cover.projection '' U) =
          U ∪ M.cover.deck ⁻¹' U := by
        ext x
        constructor
        · rintro ⟨y,hy,hxy⟩
          rcases (M.cover.fiber_pair x y).mp hxy.symm with hh | hh
          · exact Or.inl (hh ▸ hy)
          · exact Or.inr (by change M.cover.deck x ∈ U; simpa only [hh] using hy)
        · rintro (hx | hx)
          · exact ⟨x,hx,rfl⟩
          · exact ⟨M.cover.deck x,hx,M.cover.projection_deck x⟩
      rw [heq]
      exact hU.union (hU.preimage M.cover.deck.continuous)
    rw [hTb,N.boundary_eq_frontier,
      hopen.preimage_frontier_eq_frontier_preimage M.cover.projection_continuous,
      h.image_frontier]

end CurveComplex.HyperellipticModel
