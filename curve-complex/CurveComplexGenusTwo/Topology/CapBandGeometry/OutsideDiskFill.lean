import CurveComplexGenusTwo.Topology.CapBandGeometry.SquareSideCap
import CurveComplexGenusTwo.Topology.CapBandGeometry.BandSideCap
import CurveComplexGenusTwo.Topology.CapBandGeometry.FiniteFrontier
import CurveComplexGenusTwo.Dictionary.Genus

open Set Topology unitInterval
namespace CurveComplex.CapBandGeometry

theorem embedded_cap_regular_closed
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    (f : C(CapDisk, S)) (hf : IsEmbedding f) :
    closure (interior (Set.range f)) = Set.range f := by
  apply embedded_planar_region_regular_closed _ (isCompact_closedBall _ _) _ f hf
  rw [interior_closedBall _ (by norm_num : (1 : ℝ) ≠ 0),
    closure_ball _ (by norm_num : (1 : ℝ) ≠ 0)]

theorem regular_closed_union {S : Type} [TopologicalSpace S]
    {A B : Set S} (hA : IsClosed A) (hB : IsClosed B)
    (hAr : closure (interior A) = A) (hBr : closure (interior B) = B) :
    closure (interior (A ∪ B)) = A ∪ B := by
  apply subset_antisymm (closure_minimal interior_subset (hA.union hB))
  apply union_subset
  · conv_lhs => rw [← hAr]
    exact closure_mono (interior_mono subset_union_left)
  · conv_lhs => rw [← hBr]
    exact closure_mono (interior_mono subset_union_right)

theorem actual_band_outside_fill
    {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace CapPlane S]
    [PreconnectedSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b) (B : CompatibleOutsideBands D)
    {c : Curve S} (hfront : frontier (bandUnion D B) = c.image)
    (f : C(CapDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' capBoundary = c.image)
    (houtside : f '' capInterior ⊆ interior (bandUnion D B)ᶜ) :
    bandUnion D B ∪ Set.range f = Set.univ := by
  let N := bandUnion D B
  let A := N ∪ Set.range f
  let corners : Set (SupSquare D.radius) :=
    {z | |(z : ℝ × ℝ).1| = D.radius ∧ |(z : ℝ × ℝ).2| = D.radius}
  have hcorners : corners.Finite := by
    have hfin : (({D.radius, -D.radius} : Set ℝ) ×ˢ
        ({D.radius, -D.radius} : Set ℝ)).Finite := (by simp : ({D.radius, -D.radius} : Set ℝ).Finite).prod (by simp)
    apply (hfin.preimage (f := fun z : SupSquare D.radius => (z : ℝ × ℝ))
      Subtype.val_injective.injOn).subset
    intro z hz
    exact ⟨by simpa only [mem_insert_iff, mem_singleton_iff] using (abs_eq D.radius_pos.le).mp hz.1,
      by simpa only [mem_insert_iff, mem_singleton_iff] using (abs_eq D.radius_pos.le).mp hz.2⟩
  let ends : Set (I × BandWidth) := ({0, 1} : Set I) ×ˢ
    ({⟨-1, by norm_num⟩, ⟨1, by norm_num⟩} : Set BandWidth)
  have hends : ends.Finite := (by simp : ({0, 1} : Set I).Finite).prod (by simp)
  let E := D.square '' corners ∪ B.first '' ends ∪ B.second '' ends
  have hE : E.Finite := ((hcorners.image D.square).union (hends.image B.first)).union
    (hends.image B.second)
  have hN : IsClosed N := (compatibleOutsideBands_compact_connected_cover_probe D B).1.isClosed
  have hfclosed : IsClosed (Set.range f) := (isCompact_range f.continuous).isClosed
  have hA : IsClosed A := hN.union hfclosed
  have hreg : closure (interior A) = A := regular_closed_union hN hfclosed
    (compatibleOutsideBands_regular_closed D B) (embedded_cap_regular_closed f hf)
  have hfrontA : frontier A ⊆ c.image := by
    apply (frontier_union_subset N (Set.range f)).trans
    intro y hy
    rcases hy with hy | hy
    · exact hfront ▸ hy.1
    · exact hboundary ▸ embedded_disk_frontier_subset_boundary f hf hy.2
  have hfinite : (frontier A).Finite := hE.subset (by
    intro y hy
    have hyN : y ∈ frontier N := hfront.symm ▸ hfrontA hy
    have hnot : y ∉ interior A := hy.2
    change y ∈ frontier (Set.range D.square ∪ Set.range B.first ∪ Set.range B.second) at hyN
    rw [compatibleOutsideBands_frontier_eq_exposed_square_union_laterals D B] at hyN
    rcases hyN with (hsquare | hfirst) | hsecond
    · obtain ⟨z, hzy, hz, hb1, hb2⟩ := hsquare
      have hz' : (z : ℝ × ℝ) ∈ Metric.sphere ((0, 0) : ℝ × ℝ) D.radius := by
        rwa [frontier_closedBall _ D.radius_pos.ne'] at hz
      by_cases hc : |(z : ℝ × ℝ).1| = D.radius ∧ |(z : ℝ × ℝ).2| = D.radius
      · exact Or.inl (Or.inl ⟨z, hc, hzy⟩)
      · exact False.elim (hnot (hzy ▸ actual_band_exposed_square_cap_interior
          D B hfront f hf hboundary houtside z hz' hc (hzy ▸ hb1) (hzy ▸ hb2)))
    · rcases hfirst with ⟨t, hty⟩ | ⟨t, hty⟩ <;>
        by_cases ht : t = 0 ∨ t = 1
      · exact Or.inl (Or.inr ⟨(t, ⟨-1, by norm_num⟩), ⟨by simpa using ht, by simp⟩, hty⟩)
      · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he; exact ht (Or.inl (Subtype.ext he.symm)))
        have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
          intro he; exact ht (Or.inr (Subtype.ext he)))
        exact False.elim (hnot (hty ▸ actual_band_first_lateral_cap_interior D B
          hfront f hf hboundary houtside t ht0 ht1 ⟨-1, by norm_num⟩ (Or.inl rfl)))
      · exact Or.inl (Or.inr ⟨(t, ⟨1, by norm_num⟩), ⟨by simpa using ht, by simp⟩, hty⟩)
      · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he; exact ht (Or.inl (Subtype.ext he.symm)))
        have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
          intro he; exact ht (Or.inr (Subtype.ext he)))
        exact False.elim (hnot (hty ▸ actual_band_first_lateral_cap_interior D B
          hfront f hf hboundary houtside t ht0 ht1 ⟨1, by norm_num⟩ (Or.inr rfl)))
    · rcases hsecond with ⟨t, hty⟩ | ⟨t, hty⟩ <;>
        by_cases ht : t = 0 ∨ t = 1
      · exact Or.inr ⟨(t, ⟨-1, by norm_num⟩), ⟨by simpa using ht, by simp⟩, hty⟩
      · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he; exact ht (Or.inl (Subtype.ext he.symm)))
        have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
          intro he; exact ht (Or.inr (Subtype.ext he)))
        exact False.elim (hnot (hty ▸ actual_band_second_lateral_cap_interior D B
          hfront f hf hboundary houtside t ht0 ht1 ⟨-1, by norm_num⟩ (Or.inl rfl)))
      · exact Or.inr ⟨(t, ⟨1, by norm_num⟩), ⟨by simpa using ht, by simp⟩, hty⟩
      · have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.property.1 (by
          intro he; exact ht (Or.inl (Subtype.ext he.symm)))
        have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.property.2 (by
          intro he; exact ht (Or.inr (Subtype.ext he)))
        exact False.elim (hnot (hty ▸ actual_band_second_lateral_cap_interior D B
          hfront f hf hboundary houtside t ht0 ht1 ⟨1, by norm_num⟩ (Or.inr rfl))))
  have hempty := regular_closed_finite_frontier_empty A hA hreg hfinite
  rcases frontier_eq_empty_iff.mp hempty with hzero | hfull
  · have hy : f ⟨0, by simp⟩ ∈ A := Or.inr ⟨⟨0, by simp⟩, rfl⟩
    rw [hzero] at hy
    exact False.elim hy
  · exact hfull

#print axioms actual_band_outside_fill
end CurveComplex.CapBandGeometry
