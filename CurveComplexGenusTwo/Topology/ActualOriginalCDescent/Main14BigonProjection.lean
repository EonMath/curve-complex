import CurveComplexGenusTwo.Topology.IntersectionParity.BigonDiskData
import CurveComplexGenusTwo.Dictionary.BranchedCover

namespace CurveComplex

namespace BranchedDoubleCover

/-- A region disjoint from its deck translate has no identified pair. -/
theorem projection_injOn_of_disjoint_deck
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {A : Set E}
    (hA : Disjoint A (q.deck '' A)) : Set.InjOn q.projection A := by
  intro x hx y hy hxy
  rcases (q.fiber_pair x y).mp hxy with he | he
  · exact he.symm
  · exact False.elim (Set.disjoint_left.mp hA hy ⟨x,hx,he.symm⟩)

/-- The same literal region misses every branch fiber. -/
theorem projection_image_disjoint_branch_of_disjoint_deck
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) {A : Set E}
    (hA : Disjoint A (q.deck '' A)) :
    Disjoint (q.projection '' A) (q.branch : Set S) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x,hx,rfl⟩ hz
  have hfix := (q.fixed_iff_branch x).mpr hz
  exact Set.disjoint_left.mp hA hx ⟨x,hx,hfix⟩

end BranchedDoubleCover

namespace LocalSurgery

/-- Transport the *entire actual disk*, including both sides and its interior,
through the double cover once the source innermost-disk disjointness is known.
No covering-map assertion is used at a ramification point. -/
noncomputable def TwoCurveDisk.project
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) {a b : Curve E} (B : TwoCurveDisk a b)
    (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image)
    (hdis : Disjoint (Set.range B.disk) (q.deck '' Set.range B.disk)) :
    TwoCurveDisk c d := by
  let p : C(E,S) := ⟨q.projection,q.projection_continuous⟩
  have hi := q.projection_injOn_of_disjoint_deck hdis
  have sideIn (f : C(Interval,E))
      (hf : Set.range f ⊆ Set.range B.firstSide ∪ Set.range B.secondSide) :
      Set.range f ⊆ Set.range B.disk := by
    intro x hx
    obtain ⟨u,hu,he⟩ := B.boundary_eq.symm ▸ hf hx
    exact ⟨u,he⟩
  have hfirst : Set.range B.firstSide ⊆ Set.range B.disk :=
    sideIn _ (by intro x hx; exact Or.inl hx)
  have hsecond : Set.range B.secondSide ⊆ Set.range B.disk :=
    sideIn _ (by intro x hx; exact Or.inr hx)
  have hfi : Function.Injective (p.comp B.firstSide) := by
    intro t u he
    exact B.first_embedded.injective (hi (hfirst ⟨t,rfl⟩) (hfirst ⟨u,rfl⟩) he)
  have hsi : Function.Injective (p.comp B.secondSide) := by
    intro t u he
    exact B.second_embedded.injective (hi (hsecond ⟨t,rfl⟩) (hsecond ⟨u,rfl⟩) he)
  have hdi : Function.Injective (p.comp B.disk) := by
    intro t u he
    exact B.disk_embedded.injective (hi ⟨t,rfl⟩ ⟨u,rfl⟩ he)
  refine {
    firstCorner := q.projection B.firstCorner
    secondCorner := q.projection B.secondCorner
    corners_ne := ?_
    firstSide := p.comp B.firstSide
    secondSide := p.comp B.secondSide
    first_embedded := ((p.comp B.firstSide).continuous.isClosedEmbedding hfi).isEmbedding
    second_embedded := ((p.comp B.secondSide).continuous.isClosedEmbedding hsi).isEmbedding
    first_zero := congrArg q.projection B.first_zero
    second_zero := congrArg q.projection B.second_zero
    first_one := congrArg q.projection B.first_one
    second_one := congrArg q.projection B.second_one
    first_on_curve := ?_
    second_on_curve := ?_
    sides_inter := ?_
    disk := p.comp B.disk
    disk_embedded := ((p.comp B.disk).continuous.isClosedEmbedding hdi).isEmbedding
    boundary_eq := ?_ }
  · intro he
    apply B.corners_ne
    apply hi
    · exact hfirst ⟨0,B.first_zero⟩
    · exact hfirst ⟨1,B.first_one⟩
    · exact he
  · rintro x ⟨t,rfl⟩
    have h := B.first_on_curve ⟨t,rfl⟩
    rwa [ha] at h
  · rintro x ⟨t,rfl⟩
    have h := B.second_on_curve ⟨t,rfl⟩
    rwa [hb] at h
  · apply Set.Subset.antisymm
    · rintro z ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      have he : B.firstSide t = B.secondSide u :=
        hi (hfirst ⟨t,rfl⟩) (hsecond ⟨u,rfl⟩) (ht.trans hu.symm)
      have hm : B.firstSide t ∈ ({B.firstCorner,B.secondCorner} : Set E) :=
        B.sides_inter ▸ ⟨⟨t,rfl⟩,⟨u,he.symm⟩⟩
      rcases Set.mem_insert_iff.mp hm with he | he
      · exact Or.inl (ht.symm.trans (congrArg q.projection he))
      · exact Or.inr (ht.symm.trans (congrArg q.projection (Set.mem_singleton_iff.mp he)))
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with he | he
      · subst z
        exact ⟨⟨0,congrArg q.projection B.first_zero⟩,
          ⟨0,congrArg q.projection B.second_zero⟩⟩
      · have he' := Set.mem_singleton_iff.mp he
        subst z
        exact ⟨⟨1,congrArg q.projection B.first_one⟩,
          ⟨1,congrArg q.projection B.second_one⟩⟩
  · change (q.projection ∘ B.disk) '' _ =
      Set.range (q.projection ∘ B.firstSide) ∪ Set.range (q.projection ∘ B.secondSide)
    rw [Set.image_comp,B.boundary_eq,Set.image_union]
    simp only [← Set.range_comp]

theorem TwoCurveDisk.project_openInterior
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) {a b : Curve E} (B : TwoCurveDisk a b)
    (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image)
    (hdis : Disjoint (Set.range B.disk) (q.deck '' Set.range B.disk)) :
    (B.project q c d ha hb hdis).openInterior = q.projection '' B.openInterior := by
  change (q.projection ∘ B.disk) '' _ = q.projection '' (B.disk '' _)
  exact Set.image_comp _ _ _

/-- The projected disk is an actual marked-free innermost disk downstairs. -/
theorem TwoCurveDisk.project_geometry
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) {a b : Curve E} (B : TwoCurveDisk a b)
    (c d : Curve S)
    (ha : a.image = q.projection ⁻¹' c.image)
    (hb : b.image = q.projection ⁻¹' d.image)
    (hdis : Disjoint (Set.range B.disk) (q.deck '' Set.range B.disk))
    (hempty : Disjoint B.openInterior (a.image ∪ b.image)) :
    Disjoint (Set.range (B.project q c d ha hb hdis).disk) (q.branch : Set S) ∧
    Disjoint (B.project q c d ha hb hdis).openInterior (c.image ∪ d.image) := by
  constructor
  · change Disjoint (Set.range (q.projection ∘ B.disk)) (q.branch : Set S)
    rw [Set.range_comp]
    exact q.projection_image_disjoint_branch_of_disjoint_deck hdis
  · rw [B.project_openInterior q c d ha hb hdis]
    apply Set.disjoint_left.mpr
    rintro z ⟨x,hx,rfl⟩ hz
    apply Set.disjoint_left.mp hempty hx
    rcases hz with hz | hz
    · exact Or.inl (ha.symm ▸ hz)
    · exact Or.inr (hb.symm ▸ hz)

end LocalSurgery
end CurveComplex
