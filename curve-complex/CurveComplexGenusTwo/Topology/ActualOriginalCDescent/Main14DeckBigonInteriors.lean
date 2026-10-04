import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14InnermostInteriors

namespace CurveComplex.LocalSurgery

noncomputable def TwoCurveDisk.deckTranslate
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {a b : Curve E} (B : TwoCurveDisk a b)
    (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image) : TwoCurveDisk a b := by
  let D : C(E,E) := ⟨q.deck,q.deck.continuous⟩
  refine {
    firstCorner := q.deck B.firstCorner
    secondCorner := q.deck B.secondCorner
    corners_ne := fun he => B.corners_ne (q.deck.injective he)
    firstSide := D.comp B.firstSide
    secondSide := D.comp B.secondSide
    first_embedded := q.deck.isEmbedding.comp B.first_embedded
    second_embedded := q.deck.isEmbedding.comp B.second_embedded
    first_zero := congrArg q.deck B.first_zero
    second_zero := congrArg q.deck B.second_zero
    first_one := congrArg q.deck B.first_one
    second_one := congrArg q.deck B.second_one
    first_on_curve := ?_
    second_on_curve := ?_
    sides_inter := ?_
    disk := D.comp B.disk
    disk_embedded := q.deck.isEmbedding.comp B.disk_embedded
    boundary_eq := ?_ }
  · rintro z ⟨t,rfl⟩
    rw [ha]
    change q.projection (q.deck (B.firstSide t)) ∈ c.image
    rw [q.projection_deck]
    have h := B.first_on_curve ⟨t,rfl⟩
    rwa [ha] at h
  · rintro z ⟨t,rfl⟩
    rw [hb]
    change q.projection (q.deck (B.secondSide t)) ∈ d.image
    rw [q.projection_deck]
    have h := B.second_on_curve ⟨t,rfl⟩
    rwa [hb] at h
  · change Set.range (q.deck ∘ B.firstSide) ∩ Set.range (q.deck ∘ B.secondSide) = _
    rw [Set.range_comp,Set.range_comp,← Set.image_inter q.deck.injective,B.sides_inter]
    simp
  · change (q.deck ∘ B.disk) '' _ =
      Set.range (q.deck ∘ B.firstSide) ∪ Set.range (q.deck ∘ B.secondSide)
    rw [Set.image_comp,B.boundary_eq,Set.image_union]
    simp only [← Set.range_comp]

theorem TwoCurveDisk.deckTranslate_openInterior
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {a b : Curve E} (B : TwoCurveDisk a b)
    (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image) :
    (B.deckTranslate q c d ha hb).openInterior = q.deck '' B.openInterior := by
  change (q.deck ∘ B.disk) '' _ = q.deck '' (B.disk '' _)
  exact Set.image_comp _ _ _

/-- Actual deck translates of an innermost bigon have disjoint interiors.
This derives disjointness from the source inputs, not from a deck-disjointness
certificate. Boundary disjointness is the separate Step 3 of Lemma 4.5. -/
theorem innermost_two_curve_disk_deck_interiors_disjoint
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : TwoCurveDisk a.val b.val)
    (c d : Curve S)
    (ha : a.val.image = q.projection ⁻¹' c.image)
    (hb : b.val.image = q.projection ⁻¹' d.image)
    (hc : Disjoint c.image (q.branch : Set S))
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    Disjoint B.openInterior (q.deck '' B.openInterior) := by
  let C := B.deckTranslate q c d ha hb
  have hC : Disjoint C.openInterior (a.val.image ∪ b.val.image) := by
    rw [show C.openInterior = q.deck '' B.openInterior from
      B.deckTranslate_openInterior q c d ha hb]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    apply Set.disjoint_left.mp hempty hx
    rcases hz with hz | hz
    · left
      rw [ha] at hz ⊢
      change q.projection (q.deck x) ∈ c.image at hz
      rwa [q.projection_deck] at hz
    · right
      rw [hb] at hz ⊢
      change q.projection (q.deck x) ∈ d.image at hz
      rwa [q.projection_deck] at hz
  obtain hdis | heq := innermost_two_curve_disks_disjoint_or_equal B C hempty hC
  · rwa [show C.openInterior = q.deck '' B.openInterior from
      B.deckTranslate_openInterior q c d ha hb] at hdis
  · exfalso
    apply innermost_two_curve_disk_not_deck_invariant q a b ht B c ha hc hempty
    have hh : Set.range B.disk = Set.range (q.deck ∘ B.disk) := heq
    rw [Set.range_comp] at hh
    exact hh.symm

 /-- Every point of the literal innermost disk is unramified. Interior fixed
points contradict the derived interior disjointness; boundary points lie on
the two original punctured curves. -/
theorem innermost_two_curve_disk_image_disjoint_branch
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S) (a b : EssentialCurve E)
    (ht : Transverse a.val b.val) (B : TwoCurveDisk a.val b.val)
    (c d : Curve S)
    (ha : a.val.image = q.projection ⁻¹' c.image)
    (hb : b.val.image = q.projection ⁻¹' d.image)
    (hc : Disjoint c.image (q.branch : Set S))
    (hd : Disjoint d.image (q.branch : Set S))
    (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
    Disjoint (q.projection '' Set.range B.disk) (q.branch : Set S) := by
  have hdis := innermost_two_curve_disk_deck_interiors_disjoint q a b ht B c d ha hb hc hempty
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hxbranch
  by_cases hxi : x ∈ B.openInterior
  · have hfix := (q.fixed_iff_branch x).mpr hxbranch
    exact Set.disjoint_left.mp hdis hxi ⟨x,hxi,hfix⟩
  · have hxf : x ∈ frontier (Set.range B.disk) := by
      have hclosed : IsClosed (Set.range B.disk) := by
        simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
      rw [frontier,hclosed.closure_eq,embedded_surface_disk_interior_eq B.disk B.disk_embedded]
      exact ⟨hx,hxi⟩
    rw [B.frontier_range] at hxf
    rcases hxf with hxf | hxf
    · have hxcurve : x ∈ q.projection ⁻¹' c.image := ha ▸ B.first_on_curve hxf
      exact Set.disjoint_left.mp hc hxcurve hxbranch
    · have hxcurve : x ∈ q.projection ⁻¹' d.image := hb ▸ B.second_on_curve hxf
      exact Set.disjoint_left.mp hd hxcurve hxbranch

end CurveComplex.LocalSurgery
