import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.OriginalExteriorSurfaceCharts
import CurveComplexGenusTwo.Topology.ActualCompactSideDoubledCut.CutOffCentersCharts
import ClassificationOfSurfaces.Topology.InvarianceOfDomain

open Set Topology CurveComplex
open scoped Manifold ContDiff

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev FullBand := Interval × Set.Icc (-1 : ℝ) 1

theorem cutSide_isIntrinsicBoundary
    {S : Type} [TopologicalSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E))
    (i : Fin n) (b : Bool) (t : Interval) :
    letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
    (𝓡∂ 2).IsBoundaryPoint (cutSide E i b t) := by
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  obtain ⟨e,he,hzero⟩ := cutSide_boundary_chart_zero E hemb hdisjoint i b t
  apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
    (𝓡∂ 2) he).mpr
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (e (cutSide E i b t)).val 0
  exact hzero.symm

theorem cutOffCenters_isIntrinsicBoundary
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E))
    (q : CutQuotient E) (hq : cutProjection E q ∉ arcCenters E)
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (he : cutProjection E q ∈ e.source)
    (hzero : (e (cutProjection E q)).val 0 = 0) :
    letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
    (𝓡∂ 2).IsBoundaryPoint q := by
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  let y : ↥(arcCenters E)ᶜ := ⟨cutProjection E q,hq⟩
  let hne : Nonempty ↥(arcCenters E)ᶜ := ⟨y⟩
  let f := offCentersCutChart E hopen hemb hdisjoint e hne
  have hqf : q ∈ f.source := by
    rw [← offCentersCutEmbedding_of_projection E hopen hemb hdisjoint q hq]
    exact offCentersCutChart_mem_source E hopen hemb hdisjoint e hne y he
  apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isBoundaryPoint_iff_any_chart
    (𝓡∂ 2) hqf).mpr
  rw [frontier_range_modelWithCornersEuclideanHalfSpace]
  change 0 = (f q).val 0
  rw [← offCentersCutEmbedding_of_projection E hopen hemb hdisjoint q hq,
    offCentersCutChart_apply]
  exact hzero.symm

theorem cutOffCenters_isIntrinsicInterior
    {S : Type} [TopologicalSpace S] [T2Space S] [CompactSpace S] {n : ℕ}
    (E : Fin n → C(FullBand,S))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E))
    (q : CutQuotient E) (hq : cutProjection E q ∉ arcCenters E)
    (e : OpenPartialHomeomorph S (EuclideanHalfSpace 2))
    (he : cutProjection E q ∈ e.source)
    (hpos : 0 < (e (cutProjection E q)).val 0) :
    letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
    (𝓡∂ 2).IsInteriorPoint q := by
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  let y : ↥(arcCenters E)ᶜ := ⟨cutProjection E q,hq⟩
  let hne : Nonempty ↥(arcCenters E)ᶜ := ⟨y⟩
  let f := offCentersCutChart E hopen hemb hdisjoint e hne
  have hqf : q ∈ f.source := by
    rw [← offCentersCutEmbedding_of_projection E hopen hemb hdisjoint q hq]
    exact offCentersCutChart_mem_source E hopen hemb hdisjoint e hne y he
  apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
    (𝓡∂ 2) hqf).mpr
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < (f q).val 0
  rw [← offCentersCutEmbedding_of_projection E hopen hemb hdisjoint q hq,
    offCentersCutChart_apply]
  exact hpos

theorem sourceCut_core_eq_intrinsicInterior
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    [CompactSpace (OriginalBoundaryArc.Q S x R)] {n : ℕ}
    (E : Fin n → C(FullBand,OriginalBoundaryArc.Q S x R))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E)) :
    let B : Set (OriginalBoundaryArc.Q S x R) :=
      {y | y.val ∈ OriginalBoundaryArc.boundaryCircle S x R}
    letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
    cutInteriorCore E B = ModelWithCorners.interior (I := 𝓡∂ 2) (CutQuotient E) := by
  let B : Set (OriginalBoundaryArc.Q S x R) :=
    {y | y.val ∈ OriginalBoundaryArc.boundaryCircle S x R}
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  ext q
  constructor
  · intro hq
    have hoff : cutProjection E q ∉ arcCenters E := by
      exact fun hc => hq (Or.inr hc)
    have hB : (cutProjection E q).val ∉ OriginalBoundaryArc.boundaryCircle S x R := by
      exact fun hb => hq (Or.inl hb)
    obtain ⟨e,he,hpos⟩ :=
      sourceExterior_nonboundary_chart_pos S x R hR htarget (cutProjection E q) hB
    exact cutOffCenters_isIntrinsicInterior E hopen hemb hdisjoint charts q hoff e he hpos
  · intro hq
    by_contra hnot
    have hbad : cutProjection E q ∈ B ∪ arcCenters E := by
      change ¬ cutProjection E q ∈ (B ∪ arcCenters E)ᶜ at hnot
      exact not_not.mp hnot
    rcases hbad with hB | hcenter
    · by_cases hc : cutProjection E q ∈ arcCenters E
      · obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hc
        have hqside : q = cutSide E i false t ∨ q = cutSide E i true t := by
          have hf := cut_arc_center_fiber E hemb hdisjoint i t
          have : q ∈ {z : CutQuotient E |
              cutProjection E z = E i (t,⟨0,by norm_num⟩)} := by
            simpa [ht] using
              (show cutProjection E q = E i (t,⟨0,by norm_num⟩) from ht.symm)
          rw [hf] at this
          simpa using this
        rcases hqside with hqside | hqside
        · exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq
            (hqside ▸ cutSide_isIntrinsicBoundary E hemb hdisjoint charts i false t)
        · exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq
            (hqside ▸ cutSide_isIntrinsicBoundary E hemb hdisjoint charts i true t)
      · obtain ⟨e,he,hzero⟩ :=
          sourceExterior_boundary_chart_zero S x R hR htarget
            (cutProjection E q) hB
        exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq
          (cutOffCenters_isIntrinsicBoundary E hopen hemb hdisjoint
            charts q hc e he hzero)
    · obtain ⟨i,t,ht⟩ := Set.mem_iUnion.mp hcenter
      have hf := cut_arc_center_fiber E hemb hdisjoint i t
      have : q ∈ {z : CutQuotient E |
          cutProjection E z = E i (t,⟨0,by norm_num⟩)} := by
        simpa [ht] using
          (show cutProjection E q = E i (t,⟨0,by norm_num⟩) from ht.symm)
      rw [hf] at this
      rcases Set.mem_insert_iff.mp this with hside | hside
      · exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq
          (hside ▸ cutSide_isIntrinsicBoundary E hemb hdisjoint charts i false t)
      · have hside' : q = cutSide E i true t := Set.mem_singleton_iff.mp hside
        exact ((𝓡∂ 2).isInteriorPoint_iff_not_isBoundaryPoint q).mp hq
          (hside' ▸ cutSide_isIntrinsicBoundary E hemb hdisjoint charts i true t)

theorem dense_positive_euclideanHalfSpace :
    Dense {p : EuclideanHalfSpace 2 | 0 < p.val 0} := by
  let H := Set.Ici (0 : ℝ)
  have hr : Dense {r : H | 0 < r.val} := by
    apply Subtype.dense_iff.mpr
    intro r hr
    have him : (Subtype.val : H → ℝ) '' {r : H | 0 < r.val} =
        Set.Ioi (0 : ℝ) := by
      ext x
      constructor
      · rintro ⟨r,hr,rfl⟩
        exact hr
      · intro hx
        exact ⟨⟨x,by change 0 ≤ x; exact le_of_lt hx⟩,hx,rfl⟩
    rw [him, closure_Ioi]
    exact hr
  have hp : Dense {p : ℝ × H | 0 < p.2.val} := by
    have heq : (Set.univ : Set ℝ) ×ˢ {r : H | 0 < r.val} =
        {p : ℝ × H | 0 < p.2.val} := by
      ext p
      simp
    rw [← heq]
    exact (dense_univ : Dense (Set.univ : Set ℝ)).prod hr
  have h := hp.preimage halfPlaneEuclidean.symm.isOpenMap
  have hcoord (p : EuclideanHalfSpace 2) :
      (halfPlaneEuclidean.symm p).2.val = p.val 0 := by
    simpa using (halfPlaneEuclidean_coord0 (halfPlaneEuclidean.symm p)).symm
  have heq : halfPlaneEuclidean.symm ⁻¹' {p : ℝ × H | 0 < p.2.val} =
      {p : EuclideanHalfSpace 2 | 0 < p.val 0} := by
    ext p
    exact Iff.of_eq (congrArg (fun a : ℝ => 0 < a) (hcoord p))
  rw [← heq]
  exact h

theorem halfSpaceManifold_intrinsicInterior_dense
    (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 2) M] :
    Dense (ModelWithCorners.interior (I := 𝓡∂ 2) M) := by
  apply dense_iff_inter_open.mpr
  intro U hU hUnonempty
  obtain ⟨x,hxU⟩ := hUnonempty
  let e := chartAt (EuclideanHalfSpace 2) x
  have hxs : x ∈ e.source := mem_chart_source _ _
  let V : Set (EuclideanHalfSpace 2) := e '' (U ∩ e.source)
  have hVopen : IsOpen V :=
    e.isOpen_image_of_subset_source (hU.inter e.open_source) Set.inter_subset_right
  have hVnonempty : V.Nonempty :=
    ⟨e x, ⟨x, ⟨hxU,hxs⟩, rfl⟩⟩
  obtain ⟨p,hpos,⟨y,⟨hyU,hys⟩,hpy⟩⟩ :=
    dense_positive_euclideanHalfSpace.exists_mem_open hVopen hVnonempty
  refine ⟨y, hyU, ?_⟩
  apply (LeanEval.Topology.ClassificationOfSurfaces.InvarianceOfDomain.isInteriorPoint_iff_any_chart
    (𝓡∂ 2) hys).mpr
  rw [interior_range_modelWithCornersEuclideanHalfSpace]
  change 0 < (e y).val 0
  exact hpy ▸ hpos

theorem sourceCut_core_dense
    (S : Type) [TopologicalSpace S] [T2Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt (EuclideanSpace ℝ (Fin 2)) x) x) R ⊆
      (chartAt (EuclideanSpace ℝ (Fin 2)) x).target)
    [CompactSpace (OriginalBoundaryArc.Q S x R)] {n : ℕ}
    (E : Fin n → C(FullBand,OriginalBoundaryArc.Q S x R))
    (hopen : ∀ i, IsOpen (bandInterior E i))
    (hemb : ∀ i, Topology.IsEmbedding (E i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (Set.range (E i)) (Set.range (E j)))
    (charts : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E)) :
    let B : Set (OriginalBoundaryArc.Q S x R) :=
      {y | y.val ∈ OriginalBoundaryArc.boundaryCircle S x R}
    letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
    closure (cutInteriorCore E B) = Set.univ := by
  letI : ChartedSpace (EuclideanHalfSpace 2) (CutQuotient E) := charts
  dsimp only
  rw [sourceCut_core_eq_intrinsicInterior S x R hR htarget E hopen hemb hdisjoint charts]
  exact (halfSpaceManifold_intrinsicInterior_dense (CutQuotient E)).closure_eq

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
