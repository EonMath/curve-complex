import CurveComplexGenusTwo.Topology.ActualOriginalCDescent.Main14PairedSupportedTransversality

namespace CurveComplex.HyperellipticModel
open Set Topology

private theorem chosen_paired_crossing_descends
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a ao b bo : Curve E) (c d : Curve S)
    (ha : a.image ∪ ao.image = q.projection ⁻¹' c.image)
    (hb : b.image ∪ bo.image = q.projection ⁻¹' d.image)
    (hAd : Disjoint a.image ao.image)
    (hBd : Disjoint b.image bo.image)
    (hfree : Disjoint c.image (q.branch : Set S))
    (x : E) (hx : x ∈ a.image ∩ b.image)
    (hcross : CrossesAt a b x) :
    CrossesAt c d (q.projection x) := by
  have hyc : q.projection x ∈ c.image := by
    have h : x ∈ a.image ∪ ao.image := Or.inl hx.1
    rw [ha] at h
    exact h
  have hregular : q.projection x ∈ (q.branch : Set S)ᶜ :=
    fun h => Set.disjoint_left.mp hfree hyc h
  obtain ⟨G, hxG, hG⟩ :=
    q.unbranched_cover.isLocalHomeomorphOn x hregular
  obtain ⟨F, hxF, hFU, hF0, hFa, hFb⟩ :=
    source_crossing_open_partial_chart hcross Set.univ isOpen_univ
      (Set.mem_univ x)
  let W : Set E := (ao.image ∪ bo.image)ᶜ
  have hW : IsOpen W :=
    ((isCompact_range ao.embedded.continuous).isClosed.union
      (isCompact_range bo.embedded.continuous).isClosed).isOpen_compl
  have hxW : x ∈ W := by
    rintro (hxA | hxB)
    · exact Set.disjoint_left.mp hAd hx.1 hxA
    · exact Set.disjoint_left.mp hBd hx.2 hxB
  let G' := G.restrOpen W hW
  let T := G'.symm.trans F
  have hGx : G x = q.projection x := (congrFun hG x).symm
  have hxG' : x ∈ G'.source := ⟨hxG, hxW⟩
  have hyG' : q.projection x ∈ G'.target := by
    rw [← hGx]
    exact G'.map_source hxG'
  have hinv : G'.symm (q.projection x) = x := by
    rw [← hGx]
    exact G'.left_inv hxG'
  have hyT : q.projection x ∈ T.source := by
    change q.projection x ∈ G'.target ∩ G'.symm ⁻¹' F.source
    exact ⟨hyG', by simpa only [Set.mem_preimage, hinv] using hxF⟩
  have hT0 : T (q.projection x) = (0, 0) := by
    change F (G'.symm (q.projection x)) = (0, 0)
    rw [hinv, hF0]
  refine ⟨T.source, T.target, hyT, T.toHomeomorphSourceTarget,
    T.open_source, T.open_target, hT0, ?_⟩
  intro z hz
  have hzG : z ∈ G'.target := hz.1
  let y := G'.symm z
  have hyG : y ∈ G.source := (G'.map_target hzG).1
  have hyW : y ∈ W := (G'.map_target hzG).2
  have hproj : q.projection y = z := by
    have hGY : G y = z := G'.right_inv hzG
    exact (congrFun hG y).trans hGY
  have hca : z ∈ c.image ↔ y ∈ a.image := by
    rw [← hproj]
    constructor
    · intro hzC
      have hh : y ∈ a.image ∪ ao.image := by
        rw [ha]
        exact hzC
      rcases hh with hh | hh
      · exact hh
      · exact False.elim (hyW (Or.inl hh))
    · intro hyA
      have hh : y ∈ a.image ∪ ao.image := Or.inl hyA
      rw [ha] at hh
      exact hh
  have hdb : z ∈ d.image ↔ y ∈ b.image := by
    rw [← hproj]
    constructor
    · intro hzD
      have hh : y ∈ b.image ∪ bo.image := by
        rw [hb]
        exact hzD
      rcases hh with hh | hh
      · exact hh
      · exact False.elim (hyW (Or.inr hh))
    · intro hyB
      have hh : y ∈ b.image ∪ bo.image := Or.inl hyB
      rw [hb] at hh
      exact hh
  have hyF : y ∈ F.source := hz.2
  exact ⟨hca.trans (hFa y hyF), hdb.trans (hFb y hyF)⟩

theorem transverse_paired_four_component_preimages_descends
    {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E] [ClosedSurface E]
    (q : BranchedDoubleCover E S)
    (a0 a1 b0 b1 : Curve E) (c d : Curve S)
    (ha : a0.image ∪ a1.image = q.projection ⁻¹' c.image)
    (hb : b0.image ∪ b1.image = q.projection ⁻¹' d.image)
    (hAd : Disjoint a0.image a1.image)
    (hBd : Disjoint b0.image b1.image)
    (hfree : Disjoint c.image (q.branch : Set S))
    (ht00 : Transverse a0 b0)
    (ht01 : Transverse a0 b1)
    (ht10 : Transverse a1 b0)
    (ht11 : Transverse a1 b1) :
    Transverse c d := by
  let X : Set E := (a0.image ∪ a1.image) ∩ (b0.image ∪ b1.image)
  have hXfin : X.Finite := by
    apply ((((ht00.1.union ht01.1).union ht10.1).union ht11.1)).subset
    intro x hx
    rcases hx.1 with hA | hA <;> rcases hx.2 with hB | hB
    · exact Or.inl (Or.inl (Or.inl ⟨hA, hB⟩))
    · exact Or.inl (Or.inl (Or.inr ⟨hA, hB⟩))
    · exact Or.inl (Or.inr ⟨hA, hB⟩)
    · exact Or.inr ⟨hA, hB⟩
  have hproj : q.projection '' X = c.image ∩ d.image := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      constructor
      · have h := hx.1
        rw [ha] at h
        exact h
      · have h := hx.2
        rw [hb] at h
        exact h
    · intro hy
      obtain ⟨x, rfl⟩ := q.projection_surjective y
      refine ⟨x, ?_, rfl⟩
      exact ⟨by simpa only [ha, Set.mem_preimage] using hy.1,
        by simpa only [hb, Set.mem_preimage] using hy.2⟩
  refine ⟨by rw [← hproj]; exact hXfin.image q.projection, ?_⟩
  intro y hy
  obtain ⟨x, rfl⟩ := q.projection_surjective y
  have hxA : x ∈ a0.image ∪ a1.image := by
    rw [ha]
    exact hy.1
  have hxB : x ∈ b0.image ∪ b1.image := by
    rw [hb]
    exact hy.2
  rcases hxA with hxA | hxA <;> rcases hxB with hxB | hxB
  · exact chosen_paired_crossing_descends q a0 a1 b0 b1 c d
      ha hb hAd hBd hfree x ⟨hxA, hxB⟩ (ht00.2 x ⟨hxA, hxB⟩)
  · exact chosen_paired_crossing_descends q a0 a1 b1 b0 c d
      ha ((Set.union_comm _ _).trans hb) hAd hBd.symm hfree
      x ⟨hxA, hxB⟩ (ht01.2 x ⟨hxA, hxB⟩)
  · exact chosen_paired_crossing_descends q a1 a0 b0 b1 c d
      ((Set.union_comm _ _).trans ha) hb hAd.symm hBd hfree
      x ⟨hxA, hxB⟩ (ht10.2 x ⟨hxA, hxB⟩)
  · exact chosen_paired_crossing_descends q a1 a0 b1 b0 c d
      ((Set.union_comm _ _).trans ha) ((Set.union_comm _ _).trans hb)
      hAd.symm hBd.symm hfree x ⟨hxA, hxB⟩ (ht11.2 x ⟨hxA, hxB⟩)

end CurveComplex.HyperellipticModel
