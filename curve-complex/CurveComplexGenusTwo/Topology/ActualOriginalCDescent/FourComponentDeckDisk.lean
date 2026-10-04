import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.FourComponentInnermost
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14InnermostInteriors
import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.ThirdComponentCleanSide

namespace CurveComplex.LocalSurgery
open Set Topology

theorem globally_innermost_disks_interiors_disjoint_or_equal
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    {a b c d : Curve E} (B : TwoCurveDisk a b) (C : TwoCurveDisk c d)
    (U : Set E)
    (hBside : range B.firstSide ∪ range B.secondSide ⊆ U)
    (hCside : range C.firstSide ∪ range C.secondSide ⊆ U)
    (hB : Disjoint B.openInterior U)
    (hC : Disjoint C.openInterior U) :
    Disjoint B.openInterior C.openInterior ∨ range B.disk = range C.disk := by
  by_cases hdis : Disjoint B.openInterior C.openInterior
  · exact Or.inl hdis
  · right
    have hnon : (B.openInterior ∩ C.openInterior).Nonempty :=
      Set.not_disjoint_iff_nonempty_inter.mp hdis
    have subsetInterior {e f g h : Curve E} (P : TwoCurveDisk e f) (Q : TwoCurveDisk g h)
        (hQside : range Q.firstSide ∪ range Q.secondSide ⊆ U)
        (hP : Disjoint P.openInterior U)
        (hnon : (P.openInterior ∩ Q.openInterior).Nonempty) :
        P.openInterior ⊆ Q.openInterior := by
      apply P.isPreconnected_openInterior.subset_of_closure_inter_subset
        (embedded_surface_disk_interior_isOpen Q.disk Q.disk_embedded) hnon
      rintro x ⟨hx, hxP⟩
      by_contra hxnot
      have hxF : x ∈ frontier (range Q.disk) := by
        change x ∈ closure Q.openInterior at hx
        rw [Q.closure_openInterior] at hx
        change x ∈ closure (range Q.disk) \ interior (range Q.disk)
        have hclosed : IsClosed (range Q.disk) := by
          simpa only [Set.image_univ] using
            (isCompact_univ.image Q.disk.continuous).isClosed
        rw [hclosed.closure_eq,
          embedded_surface_disk_interior_eq Q.disk Q.disk_embedded]
        exact ⟨hx, hxnot⟩
      exact Set.disjoint_left.mp hP hxP (hQside (Q.frontier_range ▸ hxF))
    have heq : B.openInterior = C.openInterior := Set.Subset.antisymm
      (subsetInterior B C hCside hB hnon)
      (subsetInterior C B hBside hC (by simpa only [Set.inter_comm] using hnon))
    rw [← B.closure_openInterior, ← C.closure_openInterior, heq]

noncomputable def TwoCurveDisk.deckTranslatePaired
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {a a' b b' : Curve E}
    (D : TwoCurveDisk a b)
    (ha : q.deck '' a.image = a'.image)
    (hb : q.deck '' b.image = b'.image) : TwoCurveDisk a' b' := by
  let F : C(E, E) := ⟨q.deck, q.deck.continuous⟩
  refine {
    firstCorner := q.deck D.firstCorner
    secondCorner := q.deck D.secondCorner
    corners_ne := fun he => D.corners_ne (q.deck.injective he)
    firstSide := F.comp D.firstSide
    secondSide := F.comp D.secondSide
    first_embedded := q.deck.isEmbedding.comp D.first_embedded
    second_embedded := q.deck.isEmbedding.comp D.second_embedded
    first_zero := congrArg q.deck D.first_zero
    second_zero := congrArg q.deck D.second_zero
    first_one := congrArg q.deck D.first_one
    second_one := congrArg q.deck D.second_one
    first_on_curve := ?_
    second_on_curve := ?_
    sides_inter := ?_
    disk := F.comp D.disk
    disk_embedded := q.deck.isEmbedding.comp D.disk_embedded
    boundary_eq := ?_ }
  · change range (q.deck ∘ D.firstSide) ⊆ a'.image
    rw [Set.range_comp, ← ha]
    exact Set.image_mono D.first_on_curve
  · change range (q.deck ∘ D.secondSide) ⊆ b'.image
    rw [Set.range_comp, ← hb]
    exact Set.image_mono D.second_on_curve
  · change range (q.deck ∘ D.firstSide) ∩ range (q.deck ∘ D.secondSide) = _
    rw [Set.range_comp, Set.range_comp, ← Set.image_inter q.deck.injective,
      D.sides_inter]
    simp
  · change (q.deck ∘ D.disk) '' _ =
      range (q.deck ∘ D.firstSide) ∪ range (q.deck ∘ D.secondSide)
    rw [Set.image_comp, D.boundary_eq, Set.image_union]
    simp only [← Set.range_comp]

theorem TwoCurveDisk.deckTranslatePaired_openInterior
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {a a' b b' : Curve E}
    (D : TwoCurveDisk a b)
    (ha : q.deck '' a.image = a'.image)
    (hb : q.deck '' b.image = b'.image) :
    (D.deckTranslatePaired q ha hb).openInterior = q.deck '' D.openInterior := by
  change (q.deck ∘ D.disk) '' _ = q.deck '' (D.disk '' _)
  exact Set.image_comp _ _ _

theorem paired_two_curve_disk_not_deck_invariant
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hDeckA : q.deck '' a0.val.image = a1.val.image)
    (ht10 : Transverse a1.val b0.val)
    (D : TwoCurveDisk a0.val b0.val) :
    q.deck '' range D.disk ≠ range D.disk := by
  intro heq
  have hboundary : q.deck '' (range D.firstSide ∪ range D.secondSide) =
      range D.firstSide ∪ range D.secondSide := by
    rw [← D.frontier_range, q.deck.image_frontier, heq]
  have hsubset : q.deck '' range D.firstSide ⊆ a1.val.image ∩ b0.val.image := by
    intro z hz
    have hzA : z ∈ a1.val.image := by
      rw [← hDeckA]
      exact Set.image_mono D.first_on_curve hz
    have hzBoundary : z ∈ range D.firstSide ∪ range D.secondSide := by
      rw [← hboundary]
      exact Set.image_mono (fun x hx => Or.inl hx) hz
    rcases hzBoundary with hzFirst | hzSecond
    · exact False.elim (Set.disjoint_left.mp hAd (D.first_on_curve hzFirst) hzA)
    · exact ⟨hzA, D.second_on_curve hzSecond⟩
  have hinf : (q.deck '' range D.firstSide).Infinite := by
    have : Infinite Interval := Set.Icc.infinite (by norm_num : (0 : ℝ) < 1)
    rw [← Set.range_comp]
    exact Set.infinite_range_of_injective
      (q.deck.injective.comp D.first_embedded.injective)
  exact hinf (ht10.1.subset hsubset)

theorem paired_globally_empty_disk_deck_interiors_disjoint
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (ha : q.deck '' a0.val.image = a1.val.image)
    (hb : q.deck '' b0.val.image = b1.val.image)
    (ht10 : Transverse a1.val b0.val)
    (D : TwoCurveDisk a0.val b0.val)
    (U : Set E) (hU : q.deck '' U = U)
    (hSide : range D.firstSide ∪ range D.secondSide ⊆ U)
    (hclean : Disjoint D.openInterior U) :
    Disjoint D.openInterior (q.deck '' D.openInterior) := by
  let C := D.deckTranslatePaired q ha hb
  have hCside : range C.firstSide ∪ range C.secondSide ⊆ U := by
    change range (q.deck ∘ D.firstSide) ∪ range (q.deck ∘ D.secondSide) ⊆ U
    rw [Set.range_comp, Set.range_comp, ← Set.image_union, ← hU]
    exact Set.image_mono hSide
  have hCclean : Disjoint C.openInterior U := by
    rw [D.deckTranslatePaired_openInterior q ha hb]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hxU : x ∈ U := by
      rw [← hU]
      exact ⟨q.deck x, hz, q.deck_involution x⟩
    exact Set.disjoint_left.mp hclean hx hxU
  obtain hdis | heq :=
    globally_innermost_disks_interiors_disjoint_or_equal D C U hSide hCside
      hclean hCclean
  · rwa [show C.openInterior = q.deck '' D.openInterior from
      D.deckTranslatePaired_openInterior q ha hb] at hdis
  · exfalso
    apply paired_two_curve_disk_not_deck_invariant q a0 a1 b0 hAd ha ht10 D
    have himage : range C.disk = q.deck '' range D.disk := by
      change range (q.deck ∘ D.disk) = _
      rw [Set.range_comp]
    rw [himage] at heq
    exact heq.symm

theorem deck_interior_disjoint_disk_image_disjoint_branch
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a b : Curve E) (D : TwoCurveDisk a b)
    (hAfree : Disjoint a.image (q.projection ⁻¹' (q.branch : Set S)))
    (hBfree : Disjoint b.image (q.projection ⁻¹' (q.branch : Set S)))
    (hinteriors : Disjoint D.openInterior (q.deck '' D.openInterior)) :
    Disjoint (q.projection '' range D.disk) (q.branch : Set S) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ hxbranch
  by_cases hxi : x ∈ D.openInterior
  · have hfix := (q.fixed_iff_branch x).mpr hxbranch
    exact Set.disjoint_left.mp hinteriors hxi ⟨x, hxi, hfix⟩
  · have hxf : x ∈ frontier (range D.disk) := by
      have hclosed : IsClosed (range D.disk) := by
        simpa only [Set.image_univ] using (isCompact_univ.image D.disk.continuous).isClosed
      rw [frontier, hclosed.closure_eq,
        embedded_surface_disk_interior_eq D.disk D.disk_embedded]
      exact ⟨hx, hxi⟩
    rw [D.frontier_range] at hxf
    rcases hxf with hxf | hxf
    · exact Set.disjoint_left.mp hAfree (D.first_on_curve hxf) hxbranch
    · exact Set.disjoint_left.mp hBfree (D.second_on_curve hxf) hxbranch

theorem paired_globally_empty_disk_boundary_disjoint_deck
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (ha : q.deck '' a0.val.image = a1.val.image)
    (hb : q.deck '' b0.val.image = b1.val.image)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (D : TwoCurveDisk a0.val b0.val) (U : Set E)
    (hA0 : a0.val.image ⊆ U) (hA1 : a1.val.image ⊆ U)
    (hB0 : b0.val.image ⊆ U) (hB1 : b1.val.image ⊆ U)
    (hclean : Disjoint D.openInterior U) :
    Disjoint (range D.firstSide ∪ range D.secondSide)
      (q.deck '' (range D.firstSide ∪ range D.secondSide)) := by
  have hclean01 : Disjoint D.openInterior (a0.val.image ∪ b1.val.image) :=
    hclean.mono_right (Set.union_subset hA0 hB1)
  have hNoFirst : Disjoint (range D.firstSide) b1.val.image :=
    third_component_misses_clean_disk_side a0 b1 b0 ht01 D hBd.symm hclean01
  let R : TwoCurveDisk b0.val a0.val := {
    firstCorner := D.firstCorner, secondCorner := D.secondCorner,
    corners_ne := D.corners_ne, firstSide := D.secondSide, secondSide := D.firstSide,
    first_embedded := D.second_embedded, second_embedded := D.first_embedded,
    first_zero := D.second_zero, second_zero := D.first_zero,
    first_one := D.second_one, second_one := D.first_one,
    first_on_curve := D.second_on_curve, second_on_curve := D.first_on_curve,
    sides_inter := by rw [Set.inter_comm]; exact D.sides_inter,
    disk := D.disk, disk_embedded := D.disk_embedded,
    boundary_eq := by rw [D.boundary_eq, Set.union_comm] }
  have hclean10 : Disjoint R.openInterior (b0.val.image ∪ a1.val.image) :=
    hclean.mono_right (Set.union_subset hB0 hA1)
  have hNoSecond : Disjoint (range D.secondSide) a1.val.image :=
    third_component_misses_clean_disk_side b0 a1 a0
      (transverse_symm_of_chart ht10) R hAd.symm hclean10
  let C := D.deckTranslatePaired q ha hb
  have hboundaryImage : range C.firstSide ∪ range C.secondSide =
      q.deck '' (range D.firstSide ∪ range D.secondSide) := by
    change range (q.deck ∘ D.firstSide) ∪ range (q.deck ∘ D.secondSide) = _
    rw [Set.range_comp, Set.range_comp, Set.image_union]
  rw [← hboundaryImage]
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact Set.disjoint_left.mp hAd (D.first_on_curve hx) (C.first_on_curve hy)
  · exact Set.disjoint_left.mp hNoFirst hx (C.second_on_curve hy)
  · exact Set.disjoint_left.mp hNoSecond hx (C.first_on_curve hy)
  · exact Set.disjoint_left.mp hBd (D.second_on_curve hx) (C.second_on_curve hy)

theorem globally_empty_disks_closed_disjoint
    {E : Type} [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    {a b c d : Curve E} (B : TwoCurveDisk a b) (C : TwoCurveDisk c d)
    (U : Set E)
    (hBside : range B.firstSide ∪ range B.secondSide ⊆ U)
    (hCside : range C.firstSide ∪ range C.secondSide ⊆ U)
    (hBclean : Disjoint B.openInterior U)
    (hCclean : Disjoint C.openInterior U)
    (hOpen : Disjoint B.openInterior C.openInterior)
    (hBoundary : Disjoint (range B.firstSide ∪ range B.secondSide)
      (range C.firstSide ∪ range C.secondSide)) :
    Disjoint (range B.disk) (range C.disk) := by
  have boundaryMem {e f : Curve E} (D : TwoCurveDisk e f) {x : E}
      (hx : x ∈ range D.disk) (hxi : x ∉ D.openInterior) :
      x ∈ range D.firstSide ∪ range D.secondSide := by
    rw [← D.frontier_range]
    have hclosed : IsClosed (range D.disk) := by
      simpa only [Set.image_univ] using (isCompact_univ.image D.disk.continuous).isClosed
    rw [frontier, hclosed.closure_eq,
      embedded_surface_disk_interior_eq D.disk D.disk_embedded]
    exact ⟨hx, hxi⟩
  apply Set.disjoint_left.mpr
  intro x hxB hxC
  by_cases hBi : x ∈ B.openInterior <;> by_cases hCi : x ∈ C.openInterior
  · exact Set.disjoint_left.mp hOpen hBi hCi
  · exact Set.disjoint_left.mp hBclean hBi (hCside (boundaryMem C hxC hCi))
  · exact Set.disjoint_left.mp hCclean hCi (hBside (boundaryMem B hxB hBi))
  · exact Set.disjoint_left.mp hBoundary (boundaryMem B hxB hBi)
      (boundaryMem C hxC hCi)

theorem paired_globally_empty_disk_disjoint_deck
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 : EssentialCurve E)
    (hAd : Disjoint a0.val.image a1.val.image)
    (hBd : Disjoint b0.val.image b1.val.image)
    (ha : q.deck '' a0.val.image = a1.val.image)
    (hb : q.deck '' b0.val.image = b1.val.image)
    (ht01 : Transverse a0.val b1.val)
    (ht10 : Transverse a1.val b0.val)
    (D : TwoCurveDisk a0.val b0.val) (U : Set E)
    (hU : q.deck '' U = U)
    (hA0 : a0.val.image ⊆ U) (hA1 : a1.val.image ⊆ U)
    (hB0 : b0.val.image ⊆ U) (hB1 : b1.val.image ⊆ U)
    (hclean : Disjoint D.openInterior U) :
    Disjoint (range D.disk) (q.deck '' range D.disk) := by
  let C := D.deckTranslatePaired q ha hb
  have hSide : range D.firstSide ∪ range D.secondSide ⊆ U :=
    Set.union_subset (D.first_on_curve.trans hA0) (D.second_on_curve.trans hB0)
  have hCside : range C.firstSide ∪ range C.secondSide ⊆ U := by
    change range (q.deck ∘ D.firstSide) ∪ range (q.deck ∘ D.secondSide) ⊆ U
    rw [Set.range_comp, Set.range_comp, ← Set.image_union, ← hU]
    exact Set.image_mono hSide
  have hCclean : Disjoint C.openInterior U := by
    rw [D.deckTranslatePaired_openInterior q ha hb]
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ hz
    have hxU : x ∈ U := by
      rw [← hU]
      exact ⟨q.deck x, hz, q.deck_involution x⟩
    exact Set.disjoint_left.mp hclean hx hxU
  have hOpen : Disjoint D.openInterior C.openInterior := by
    rw [D.deckTranslatePaired_openInterior q ha hb]
    exact paired_globally_empty_disk_deck_interiors_disjoint
      q a0 a1 b0 b1 hAd ha hb ht10 D U hU hSide hclean
  have hBoundary : Disjoint
      (range D.firstSide ∪ range D.secondSide)
      (range C.firstSide ∪ range C.secondSide) := by
    have h := paired_globally_empty_disk_boundary_disjoint_deck q
      a0 a1 b0 b1 hAd hBd ha hb ht01 ht10 D U
      hA0 hA1 hB0 hB1 hclean
    have hEq : range C.firstSide ∪ range C.secondSide =
        q.deck '' (range D.firstSide ∪ range D.secondSide) := by
      change range (q.deck ∘ D.firstSide) ∪ range (q.deck ∘ D.secondSide) = _
      rw [Set.range_comp, Set.range_comp, Set.image_union]
    rwa [hEq]
  have hClosed := globally_empty_disks_closed_disjoint
    D C U hSide hCside hclean hCclean hOpen hBoundary
  change Disjoint (range D.disk) (range (q.deck ∘ D.disk)) at hClosed
  rwa [Set.range_comp] at hClosed

end CurveComplex.LocalSurgery
