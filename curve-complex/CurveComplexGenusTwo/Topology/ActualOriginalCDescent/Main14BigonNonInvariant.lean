import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14InvariantArc
import CurveComplexGenusTwo.Topology.IntersectionParity.EmptyDiskSidesStatement

namespace CurveComplex.LocalSurgery

theorem TwoCurveDisk.frontier_range
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    {a b : Curve E} (B : TwoCurveDisk a b) :
    frontier (Set.range B.disk) = Set.range B.firstSide ∪ Set.range B.secondSide := by
  have hclosed : IsClosed (Set.range B.disk) := by
    simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
  rw [frontier,hclosed.closure_eq,
    embedded_surface_disk_interior_eq B.disk B.disk_embedded,← B.boundary_eq]
  apply Set.Subset.antisymm
  · rintro z ⟨⟨u,rfl⟩,hz⟩
    refine ⟨u,?_,rfl⟩
    have hle : ‖u.val‖ ≤ 1 := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
    have hn : ¬ ‖u.val‖ < 1 := by
      intro h
      exact hz ⟨u,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using h,rfl⟩
    simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using
      le_antisymm hle (le_of_not_gt hn)
  · rintro z ⟨u,hu,rfl⟩
    refine ⟨⟨u,rfl⟩,?_⟩
    rintro ⟨v,hv,he⟩
    have heq := B.disk_embedded.injective he
    subst v
    have hlt : ‖u.val‖ < 1 := by
      simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hv
    have he : ‖u.val‖ = 1 := by
      simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hu
    exact (ne_of_lt hlt) he

/-- Source Lemma 4.5, Step 1: an actual innermost disk cannot be preserved
by the deck involution. Cleanliness comes from transversality and the actual
empty interior, and the contradiction is the interval fixed-point theorem. -/
theorem innermost_two_curve_disk_not_deck_invariant
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : TwoCurveDisk a.val b.val)
    (c : Curve S) (ha : a.val.image = q.projection ⁻¹' c.image)
    (hc : Disjoint c.image (q.branch : Set S))
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    q.deck '' Set.range B.disk ≠ Set.range B.disk := by
  intro heq
  have hclean := (empty_two_curve_disk_has_clean_sides a b ht B hempty).2
  have hboundary : q.deck '' (Set.range B.firstSide ∪ Set.range B.secondSide) =
      Set.range B.firstSide ∪ Set.range B.secondSide := by
    rw [← B.frontier_range,q.deck.image_frontier,heq]
  have hinv : q.deck '' Set.range B.firstSide ⊆ Set.range B.firstSide := by
    rintro z ⟨x,hx,rfl⟩
    have hxA : x ∈ q.projection ⁻¹' c.image := ha ▸ B.first_on_curve hx
    have hdeckA : q.deck x ∈ a.val.image := by
      rw [ha]
      change q.projection (q.deck x) ∈ c.image
      rwa [q.projection_deck]
    have hm : q.deck x ∈ Set.range B.firstSide ∪ Set.range B.secondSide := by
      rw [← hboundary]
      exact ⟨x,Or.inl hx,rfl⟩
    rcases hm with hm | hm
    · exact hm
    · have he : q.deck x ∈ ({B.firstCorner,B.secondCorner} : Set E) :=
        hclean ▸ ⟨hm,hdeckA⟩
      rcases Set.mem_insert_iff.mp he with he | he
      · exact ⟨0,B.first_zero.trans he.symm⟩
      · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp he).symm⟩
  apply q.unramified_embedded_interval_not_deck_invariant B.firstSide B.first_embedded ?_ hinv
  intro t htbranch
  have htcurve : B.firstSide t ∈ q.projection ⁻¹' c.image := ha ▸ B.first_on_curve ⟨t,rfl⟩
  exact Set.disjoint_left.mp hc htcurve htbranch

end CurveComplex.LocalSurgery
