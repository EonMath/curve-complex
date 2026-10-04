import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14DeckBigonInteriors
import CurveComplexGenusTwo.Topology.PositionExtension.CleanSideProjectionStatement

open Set Topology

namespace CurveComplex.BranchedDoubleCover

noncomputable def unramifiedBaseCurve
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (c : Curve S)
    (hc : Disjoint c.image (q.branch : Set S)) : Curve q.unramifiedBase := by
  let f : Circle → q.unramifiedBase :=
    fun t => ⟨c.map t,Set.disjoint_left.mp hc (Set.mem_range_self t)⟩
  exact ⟨f,IsEmbedding.subtypeVal.of_comp_iff.mp c.embedded⟩

theorem mem_unramifiedBaseCurve_image
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    (q : BranchedDoubleCover E S) (c : Curve S)
    (hc : Disjoint c.image (q.branch : Set S)) (z : q.unramifiedBase) :
    z ∈ (q.unramifiedBaseCurve c hc).image ↔ z.val ∈ c.image := by
  constructor
  · rintro ⟨t,he⟩; exact ⟨t,congrArg Subtype.val he⟩
  · rintro ⟨t,he⟩; exact ⟨t,Subtype.ext he⟩

/-- Apply canonical clean-side injectivity to the actual punctured restriction
of the raw branched cover. The only endpoint condition is literal distinction
of the projected corners; whole-disk deck disjointness is not assumed. -/
theorem clean_lifted_side_projection_embedding
    {E S : Type} [TopologicalSpace E] [T2Space E]
    [TopologicalSpace S] [T2Space S]
    (q : BranchedDoubleCover E S) (c d : Curve S)
    (hc : Disjoint c.image (q.branch : Set S))
    (hd : Disjoint d.image (q.branch : Set S))
    (α : C(Interval,E)) (hα : IsEmbedding α)
    (hαc : Set.range α ⊆ q.projection ⁻¹' c.image)
    (hclean : Set.range α ∩ q.projection ⁻¹' d.image = {α 0,α 1})
    (hcorners : q.projection (α 0) ≠ q.projection (α 1)) :
    IsEmbedding ((⟨q.projection,q.projection_continuous⟩ : C(E,S)).comp α) := by
  let a := q.unramifiedBaseCurve c hc
  let b := q.unramifiedBaseCurve d hd
  have hfree (t : Interval) : q.projection (α t) ∉ q.branch :=
    Set.disjoint_left.mp hc (hαc ⟨t,rfl⟩)
  let A : C(Interval,q.unramifiedTotal) :=
    ⟨fun t => ⟨α t,hfree t⟩,α.continuous.subtype_mk _⟩
  have hA : IsEmbedding A := IsEmbedding.subtypeVal.of_comp_iff.mp hα
  have hAa : Set.range A ⊆ q.unramifiedProjection ⁻¹' a.image := by
    rintro z ⟨t,rfl⟩
    exact (q.mem_unramifiedBaseCurve_image c hc _).mpr (hαc ⟨t,rfl⟩)
  have hAb : Set.range A ∩ q.unramifiedProjection ⁻¹' b.image = {A 0,A 1} := by
    apply Set.Subset.antisymm
    · rintro z ⟨⟨t,rfl⟩,ht⟩
      have ht' := (q.mem_unramifiedBaseCurve_image d hd _).mp ht
      have hm : α t ∈ ({α 0,α 1} : Set E) := hclean ▸ ⟨⟨t,rfl⟩,ht'⟩
      rcases Set.mem_insert_iff.mp hm with he | he
      · exact Or.inl (Subtype.ext he)
      · exact Or.inr (Subtype.ext (Set.mem_singleton_iff.mp he))
    · intro z hz
      rcases Set.mem_insert_iff.mp hz with he | he
      · subst z
        refine ⟨⟨0,rfl⟩,(q.mem_unramifiedBaseCurve_image d hd _).mpr ?_⟩
        have hm : α 0 ∈ Set.range α ∩ q.projection ⁻¹' d.image := hclean.symm ▸ (by simp)
        exact hm.2
      · have he' := Set.mem_singleton_iff.mp he
        subst z
        refine ⟨⟨1,rfl⟩,(q.mem_unramifiedBaseCurve_image d hd _).mpr ?_⟩
        have hm : α 1 ∈ Set.range α ∩ q.projection ⁻¹' d.image := hclean.symm ▸ (by simp)
        exact hm.2
  have hAcorners : q.unramifiedProjection (A 0) ≠ q.unramifiedProjection (A 1) :=
    fun he => hcorners (congrArg Subtype.val he)
  have hproj := LocalSurgery.clean_lifted_side_projects_to_embedding
    q.unramifiedProjection q.unramified_isCoveringMap a b A hA hAa hAb hAcorners
  exact IsEmbedding.subtypeVal.comp hproj

end CurveComplex.BranchedDoubleCover
