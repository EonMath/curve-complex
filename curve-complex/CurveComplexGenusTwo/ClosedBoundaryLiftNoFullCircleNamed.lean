import CurveComplexGenusTwo.Dictionary.ArcVertexAPI
open Set Topology
namespace CurveComplex.HyperellipticModel
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
 [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] (M : HyperellipticModel E S)
set_option linter.style.haveILetI false
theorem closed_boundary_lift_no_full_circle (a : PuncturedCircle M) (β : C(Interval,S))
 (hcoll : ∀ s t, β s=β t → s=t ∨ (s=0 ∧ t=1) ∨ (s=1 ∧ t=0))
 (hrange : Set.range β=a.image) (γ : C(Interval,E))
 (hπ : ∀ t, M.cover.projection (γ t)=β t) (hends : γ 0=γ 1)
 (c : Curve E) (hc : c.image=M.cover.projection ⁻¹' a.image) : False := by
 letI : ClosedSurface E := Classical.choice M.genusTwo.2.1
 let A := Set.range γ
 let B := M.cover.deck '' A
 have havoid (t) : M.cover.deck (γ t) ≠ γ t := by
   intro he
   have hb := (M.cover.fixed_iff_branch (γ t)).mp he
   rw [hπ] at hb
   have htA : β t ∈ a.image := by rw [← hrange]; exact Set.mem_range_self t
   exact Set.disjoint_left.mp a.avoids_branch htA hb
 have hAB : Disjoint A B := by
   apply Set.disjoint_left.mpr
   rintro x ⟨s,rfl⟩ ⟨y,⟨t,rfl⟩,he⟩
   have hb : β s=β t := by rw [← hπ,← hπ,← he,M.cover.projection_deck]
   rcases hcoll s t hb with rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
   · exact havoid s he
   · exact havoid 0 (by rw [← hends] at he; exact he)
   · exact havoid 0 (by rw [← hends] at he; exact he)
 have hcover : c.image=A ∪ B := by
   rw [hc,← hrange]
   ext x
   constructor
   · rintro ⟨t,ht⟩
     rcases (M.cover.fiber_pair (γ t) x).mp ((hπ t).trans ht) with he | he
     · exact Or.inl ⟨t,he.symm⟩
     · exact Or.inr ⟨γ t,⟨t,rfl⟩,he.symm⟩
   · rintro (⟨t,rfl⟩ | ⟨y,⟨t,rfl⟩,rfl⟩)
     · exact ⟨t,(hπ t).symm⟩
     · exact ⟨t,((M.cover.projection_deck _).trans (hπ t)).symm⟩
 have hAc : IsClosed A := (isCompact_range γ.continuous).isClosed
 have hBc : IsClosed B := ((isCompact_range γ.continuous).image M.cover.deck.continuous).isClosed
 have hAn : (c.image ∩ A).Nonempty := by
   refine ⟨γ 0,?_,⟨0,rfl⟩⟩
   rw [hcover]; exact Or.inl ⟨0,rfl⟩
 have hBn : (c.image ∩ B).Nonempty := by
   refine ⟨M.cover.deck (γ 0),?_,⟨γ 0,⟨0,rfl⟩,rfl⟩⟩
   rw [hcover]; exact Or.inr ⟨γ 0,⟨0,rfl⟩,rfl⟩
 obtain ⟨x,_,hxA,hxB⟩ := isPreconnected_closed_iff.mp
   (isPreconnected_range c.embedded.continuous) A B hAc hBc hcover.subset hAn hBn
 exact Set.disjoint_left.mp hAB hxA hxB
end CurveComplex.HyperellipticModel
