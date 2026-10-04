import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.HalfStripLocalCharts

open Set Topology CurveComplex
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev FullBand := Interval × Set.Icc (-1 : ℝ) 1

noncomputable def offCentersCutEmbedding
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    ↥(arcCenters E)ᶜ → CutQuotient E :=
  fun z => ((cutCoreHomeomorph E hopen hemb hdisjoint).symm z).val

theorem offCentersCutEmbedding_isOpenEmbedding
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j))) :
    Topology.IsOpenEmbedding (offCentersCutEmbedding E hopen hemb hdisjoint) := by
  letI : CompactSpace (CutQuotient E) := cutQuotient_compact E hopen
  have hcore : Topology.IsOpenEmbedding
      (Subtype.val : ↥(cutCore E) → CutQuotient E) :=
    ⟨Topology.IsEmbedding.subtypeVal, by
      simpa only [Subtype.range_coe] using cutCore_isOpen E⟩
  exact hcore.comp (cutCoreHomeomorph E hopen hemb hdisjoint).symm.isOpenEmbedding

noncomputable def offCentersCutChart
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hne : Nonempty ↥(arcCenters E)ᶜ) :
    OpenPartialHomeomorph (CutQuotient E) (EuclideanHalfSpace 2) := by
  let U : TopologicalSpace.Opens S :=
    ⟨(arcCenters E)ᶜ, (arcCenters_isClosed E).isOpen_compl⟩
  exact (e.subtypeRestr (show Nonempty U from hne)).lift_openEmbedding
    (offCentersCutEmbedding_isOpenEmbedding E hopen hemb hdisjoint)

theorem offCentersCutChart_mem_source
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hne : Nonempty ↥(arcCenters E)ᶜ)
    (z : ↥(arcCenters E)ᶜ) (hz : z.val ∈ e.source) :
    offCentersCutEmbedding E hopen hemb hdisjoint z ∈
      (offCentersCutChart E hopen hemb hdisjoint e hne).source := by
  rw [offCentersCutChart, OpenPartialHomeomorph.lift_openEmbedding_source]
  exact ⟨z, by simpa only [OpenPartialHomeomorph.subtypeRestr_source,
    Set.mem_preimage] using hz, rfl⟩

theorem offCentersCutChart_apply
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (hne : Nonempty ↥(arcCenters E)ᶜ)
    (z : ↥(arcCenters E)ᶜ) :
    (offCentersCutChart E hopen hemb hdisjoint e hne)
      (offCentersCutEmbedding E hopen hemb hdisjoint z) = e z.val := by
  rw [offCentersCutChart, OpenPartialHomeomorph.lift_openEmbedding_apply]
  rfl

theorem offCentersCutEmbedding_of_projection
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (q : CutQuotient E) (hq : cutProjection E q ∉ arcCenters E) :
    offCentersCutEmbedding E hopen hemb hdisjoint ⟨cutProjection E q,hq⟩ = q := by
  let qcore : ↥(cutCore E) := ⟨q, by simpa [cutCore] using hq⟩
  have hy : (cutCoreHomeomorph E hopen hemb hdisjoint) qcore =
      (⟨cutProjection E q,hq⟩ : ↥(arcCenters E)ᶜ) := Subtype.ext rfl
  have h := (cutCoreHomeomorph E hopen hemb hdisjoint).symm_apply_apply qcore
  rw [hy] at h
  exact congrArg Subtype.val h

theorem cutQuotient_has_halfSpace_atlas
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (hcharts : ∀ y : S,
      ∃ e : OpenPartialHomeomorph S (EuclideanHalfSpace 2), y ∈ e.source) :
    ∃ charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E),
      letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
      IsManifold (𝓡∂ 2) 0 (CutQuotient E) := by
  classical
  have hLocal : ∀ q : CutQuotient E,
      ∃ e : OpenPartialHomeomorph (CutQuotient E) (EuclideanHalfSpace 2),
        q ∈ e.source := by
    intro q
    by_cases hc : cutProjection E q ∈ arcCenters E
    · obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hc
      have hq : q = cutSide E i false t ∨ q = cutSide E i true t := by
        have hf := cut_arc_center_fiber E hemb hdisjoint i t
        have : q ∈ {z : CutQuotient E |
            cutProjection E z = E i (t,⟨0,by norm_num⟩)} := by
          simpa [ht] using (show cutProjection E q = E i (t,⟨0,by norm_num⟩) from ht.symm)
        rw [hf] at this
        simpa using this
      rcases hq with hq | hq
      · rcases halfCut_mem_endpoint_chart E hemb hdisjoint i false
          (t,⟨0,by norm_num⟩) (by norm_num [halfOpen])
          with hleft | hright
        · refine ⟨leftCutChart E hemb hdisjoint i false, ?_⟩
          rw [hq]
          exact hleft
        · refine ⟨rightCutChart E hemb hdisjoint i false, ?_⟩
          rw [hq]
          exact hright
      · rcases halfCut_mem_endpoint_chart E hemb hdisjoint i true
          (t,⟨0,by norm_num⟩) (by norm_num [halfOpen])
          with hleft | hright
        · refine ⟨leftCutChart E hemb hdisjoint i true, ?_⟩
          rw [hq]
          exact hleft
        · refine ⟨rightCutChart E hemb hdisjoint i true, ?_⟩
          rw [hq]
          exact hright
    · let y : ↥(arcCenters E)ᶜ := ⟨cutProjection E q,hc⟩
      obtain ⟨e,he⟩ := hcharts y.val
      have hne : Nonempty ↥(arcCenters E)ᶜ := ⟨y⟩
      refine ⟨offCentersCutChart E hopen hemb hdisjoint e hne, ?_⟩
      have hmatch : offCentersCutEmbedding E hopen hemb hdisjoint y = q := by
        let qcore : ↥(cutCore E) := ⟨q, by simpa [cutCore] using hc⟩
        have hy : (cutCoreHomeomorph E hopen hemb hdisjoint) qcore = y :=
          Subtype.ext rfl
        have h := (cutCoreHomeomorph E hopen hemb hdisjoint).symm_apply_apply qcore
        rw [hy] at h
        exact congrArg Subtype.val h
      rw [← hmatch]
      exact offCentersCutChart_mem_source E hopen hemb hdisjoint e hne y he
  choose localChart hSource using hLocal
  let charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := {
    atlas := Set.range localChart
    chartAt := localChart
    mem_chart_source := hSource
    chart_mem_atlas := Set.mem_range_self }
  refine ⟨charts, ?_⟩
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  infer_instance

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
