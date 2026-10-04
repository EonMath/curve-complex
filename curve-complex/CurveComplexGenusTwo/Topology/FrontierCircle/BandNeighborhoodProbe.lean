import CurveComplexGenusTwo.Topology.FrontierCircle.BandAttachmentInteriorProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.BandInteriorProbe
import CurveComplexGenusTwo.Topology.FrontierCircle.BandUnionProbe

open Set Topology unitInterval
namespace CurveComplex

theorem compatibleOutsideBands_compact_connected_neighborhood_probe
    {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D) :
    let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
    IsCompact N ∧ IsConnected N ∧ a.image ∪ b.image ⊆ interior N := by
  obtain ⟨hc,hn,hcover⟩ := compatibleOutsideBands_compact_connected_cover_probe D B
  refine ⟨hc,hn,?_⟩
  let N := Set.range D.square ∪ Set.range B.first ∪ Set.range B.second
  have hfirst : Set.range D.square ∪ Set.range B.first ⊆ N := Set.subset_union_left
  have hsecond : Set.range D.square ∪ Set.range B.second ⊆ N := by
    intro z hz
    rcases hz with h | h
    · exact Or.inl (Or.inl h)
    · exact Or.inr h
  have hp (t : I) : D.firstArc t ∈ interior N := by
    rw [← B.first_center]
    by_cases ht0 : t = 0
    · subst t
      exact interior_mono hfirst (attached_band_zero_interior_probe D B.first
        B.first_embedded 2 0 B.first_bottom B.first_top B.first_square)
    by_cases ht1 : t = 1
    · subst t
      exact interior_mono hfirst (attached_band_one_interior_probe D B.first
        B.first_embedded 2 0 B.first_bottom B.first_top B.first_square)
    apply interior_mono (fun z hz => Or.inl (Or.inr hz))
    apply embedded_rectangle_center_interior_probe B.first B.first_embedded t
    · have hne : (t:ℝ) ≠ 0 := fun he => ht0 (Subtype.ext he)
      exact lt_of_le_of_ne t.property.1 hne.symm
    · have hne : (t:ℝ) ≠ 1 := fun he => ht1 (Subtype.ext he)
      exact lt_of_le_of_ne t.property.2 hne
  have hq (t : I) : D.secondArc t ∈ interior N := by
    rw [← B.second_center]
    by_cases ht0 : t = 0
    · subst t
      exact interior_mono hsecond (attached_band_zero_interior_probe D B.second
        B.second_embedded 3 1 B.second_left B.second_right B.second_square)
    by_cases ht1 : t = 1
    · subst t
      exact interior_mono hsecond (attached_band_one_interior_probe D B.second
        B.second_embedded 3 1 B.second_left B.second_right B.second_square)
    apply interior_mono (fun z hz => Or.inr hz)
    apply embedded_rectangle_center_interior_probe B.second B.second_embedded t
    · have hne : (t:ℝ) ≠ 0 := fun he => ht0 (Subtype.ext he)
      exact lt_of_le_of_ne t.property.1 hne.symm
    · have hne : (t:ℝ) ≠ 1 := fun he => ht1 (Subtype.ext he)
      exact lt_of_le_of_ne t.property.2 hne
  intro z hz
  by_cases hO : z ∈ D.openSquare
  · have hsub : D.openSquare ⊆ N := by
      intro w hw
      rw [D.openSquare_eq] at hw
      exact Or.inl (Or.inl (Set.image_subset_range _ _ hw))
    exact (D.openSquare_open.subset_interior_iff.mpr hsub) hO
  · rcases hz with ha | hb
    · obtain ⟨t,rfl⟩ := D.firstArc_range ▸ (show z ∈ a.image \ D.openSquare from ⟨ha,hO⟩)
      exact hp t
    · obtain ⟨t,rfl⟩ := D.secondArc_range ▸ (show z ∈ b.image \ D.openSquare from ⟨hb,hO⟩)
      exact hq t

#print axioms compatibleOutsideBands_compact_connected_neighborhood_probe
end CurveComplex
