import CurveComplexGenusTwo.Filtration.Geometry.ActualRepresentativeObjects
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
theorem actual_arc_face_localization (M : HyperellipticModel E S) {I : Type} [Finite I]
    (r : I → EssentialMarkedArc M) (a : EssentialMarkedArc M)
    (hd : ∀ v, Disjoint (arcInterior M a) (arcInterior M (r v))) :
    ∃ U : Set S, IsComplementComponent (⋃ v, (r v).val.image) U ∧
      arcInterior M a ⊆ U ∧ a.val.image ⊆ closure U := by
  have hi : a.val.map '' Set.Ioo (0 : Interval) 1 = arcInterior M a := by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      refine ⟨⟨t,rfl⟩,?_⟩
      intro hb
      rcases a.val.marked_only_at_ends t hb with h | h
      · simpa [h] using ht.1
      · simpa [h] using ht.2
    · rintro ⟨⟨t,rfl⟩,hn⟩
      have ht0 : (t : ℝ) ≠ 0 := by
        intro h
        have he : t = (0 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.start_marked)
      have ht1 : (t : ℝ) ≠ 1 := by
        intro h
        have he : t = (1 : Interval) := Subtype.ext h
        exact hn (he ▸ a.val.end_marked)
      refine ⟨t,?_,rfl⟩
      change (0 : ℝ) < t.val ∧ t.val < 1
      exact ⟨lt_of_le_of_ne' t.property.1 ht0, lt_of_le_of_ne t.property.2 ht1⟩
  have hci : IsConnected (arcInterior M a) := by
    rw [← hi]
    have hc : IsConnected (Set.Ioo (0 : Interval) 1) :=
      ⟨⟨⟨(1:ℝ)/2, by constructor <;> norm_num⟩, by
          constructor
          · change (0 : ℝ) < 1/2; norm_num
          · change (1 : ℝ)/2 < 1; norm_num⟩,
        isPreconnected_Ioo⟩
    exact hc.image a.val.map a.val.continuous.continuousOn
  have hdense : a.val.image ⊆ closure (arcInterior M a) := by
    rintro y ⟨t,ht⟩
    have htcl : t ∈ closure (Set.Ioo (0 : Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
      constructor
      · change (0 : ℝ) ≤ t.val; exact t.property.1
      · change t.val ≤ (1 : ℝ); exact t.property.2
    have hm : a.val.map t ∈ closure (a.val.map '' Set.Ioo (0 : Interval) 1) :=
      image_closure_subset_closure_image a.val.continuous ⟨t,htcl,rfl⟩
    rw [hi] at hm
    exact ht ▸ hm
  let G := ⋃ v, (r v).val.image
  have havoid : arcInterior M a ⊆ Gᶜ := by
    intro x hx hxG
    obtain ⟨v,hv⟩ := Set.mem_iUnion.mp hxG
    exact Set.disjoint_left.mp (hd v) hx ⟨hv,hx.2⟩
  obtain ⟨x,hx⟩ := hci.nonempty
  let U := connectedComponentIn Gᶜ x
  have hU : IsComplementComponent G U :=
    complementComponent_iff_componentIn.mpr ⟨x,havoid hx,rfl⟩
  have hsub : arcInterior M a ⊆ U := hci.isPreconnected.subset_connectedComponentIn hx havoid
  have hclU : a.val.image ⊆ closure U := hdense.trans (closure_mono hsub)
  exact ⟨U,hU,hsub,hclU⟩
end CurveComplex.HyperellipticModel
