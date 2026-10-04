import CurveComplexGenusTwo.Topology.ActualOriginalContactSelector.ActualProperCrosscutJoinedTailKernelRecovery
import Mathlib.Analysis.Convex.Basic
import CurveComplexGenusTwo.Topology.GlobalArcCollar.AxisFramedStripProducerStatement
import CurveComplexGenusTwo.Topology.ArcTrim.SupportedStrictDiskEnlargementStatement
import CurveComplexGenusTwo.Topology.CapBandGeometry.CapSide
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualWholeInteriorAxisChart
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingAfterClosedReplacement
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ArcZeroMarkedCrossingSymmetry
import CurveComplexGenusTwo.Topology.IntersectionParity.CurveImageInclusion
import CurveComplexGenusTwo.Topology.IntersectionParity.Subdisk
import CurveComplexGenusTwo.Topology.IntersectionParity.DiskFrontierStatement
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedSideEndpointMarks
import CurveComplexGenusTwo.Topology.IntersectionParity.ArcInterior
import CurveComplexGenusTwo.Topology.ActualMain14RelativeCancellation.RawArcSubarcOpen
import ActualSameClassParallelNonloopDisk
import CurveComplexGenusTwo.Topology.ActualJoinedMarkedCarrier.ActualRawTailBigonReplacement
import CurveComplexGenusTwo.Topology.ActualOriginalLoopSelector.ActualSameClassLoopOriginalSubpathsPuncturedHomotopic
import ActualSelectedJordanComponentDisk
import CurveComplexGenusTwo.Filtration.Geometry.ActualPuncturedJordanConversion
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEssentialLoopDiskObstruction
import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualMarkFreeBigonLocalization
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import CurveComplexGenusTwo.Filtration.Geometry.ActualCompactTimeCrosscutExtraction
import CurveComplexGenusTwo.Topology.CompletedJordan
import Mathlib.Topology.Order.IntermediateValue
import Schoenflies.Concatenate
import Schoenflies.Subarc
import CurveComplexGenusTwo.Topology.Smoothing.MarkedTransport
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Schoenflies.ModelCurve
import Schoenflies.JordanSchoenflies
import CurveComplexGenusTwo.Intersection.SphereChart
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.CrosscutIsotopy
import CurveComplexGenusTwo.Filtration.Geometry.ActualSupportCrosscutAlignment
import CurveComplexGenusTwo.Dictionary.MarkedSphere
import CurveComplexGenusTwo.Intersection.SmoothArc
import CurveComplexGenusTwo.Filtration.FinalAbutment
import CurveComplexGenusTwo.Filtration.FirstPageSplit
import CurveComplexGenusTwo.Filtration.E1BridgeAssembly
import CurveComplexGenusTwo.Filtration.PageComplex
import CurveComplexGenusTwo.Filtration.FiltrationSpectralObjectFull
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ConeGeometry
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualBoundaryInteriorArcHeaders
import CurveComplexGenusTwo.Topology.RestrictedLink.ActualTwoMarkAlignedRestrictedLink

namespace CurveComplex.HyperellipticModel
open CurveGenusTwo.Filtration
open CategoryTheory
set_option maxHeartbeats 6000000
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable local instance (M : HyperellipticModel E S) :
    DecidableEq (EssentialArcClass M) := Classical.decEq _
open Set Topology Schoenflies Metric Filter
open scoped Classical

private theorem actual_original_contact_disk_cleanup_entire_pair_and_graph_private
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
    (r r0 : {w // w ∈ F} → EssentialMarkedArc M)
    (rT : {w // w ∈ T.val} → EssentialMarkedArc M)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
    (hdT : ∀ w : {w // w ∈ T.val},w.val ∈ J → Disjoint (arcInterior M (rT w)) (arcInterior M (rT u)))
    (haligned0 : ∀ w : {w // w ∈ T.val},w.val ∈ J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u))
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠(r0 ⟨u.val,hTF u.property⟩).val.map 1)
    (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
    (hcross : ∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) q)
    (hInitial : ∃ B : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      B.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        B.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
    ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
          (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
      (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) := by
  classical
  have actual_contact_disk_graph_clearance
      (firstSide newSide : C(Interval,S))
      (hfirst : range firstSide ⊆ (r0 ⟨u.val,hTF u.property⟩).val.image)
      (hnew : range newSide ⊆ (rT u).val.image)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hdisk : IsEmbedding d) (p q : S)
      (hmarks : Disjoint
        (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S))
      (hcorners : ∀ z ∈ range d, z ∈ M.cover.branch → z=p ∨ z=q)
      (hcontact : p ∉ M.cover.branch ∨ q ∉ M.cover.branch)
      (hboundary : d '' {x | x.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1}=range firstSide ∪ range newSide) :
      Disjoint (d '' {x | x.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1}) (actualObjectTrace M r J) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨corner,hcorner⟩ : ∃ corner : S,
        ∀ z ∈ range d, z ∈ M.cover.branch → z=corner := by
      rcases hcontact with hp | hq
      · refine ⟨q,?_⟩
        intro z hz hzm
        rcases hcorners z hz hzm with he | he
        · exact False.elim (hp (he ▸ hzm))
        · exact he
      · refine ⟨p,?_⟩
        intro z hz hzm
        rcases hcorners z hz hzm with he | he
        · exact he
        · exact False.elim (hq (he ▸ hzm))
    let U := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    let H := range firstSide ∪ range newSide
    have hU := actual_embedded_disk_interior_component M d hdisk
    rw [hboundary] at hU
    apply disjoint_left.mpr
    intro z hzU hzG
    rw [←hgraph] at hzG
    obtain ⟨v,hv⟩ := mem_iUnion.mp hzG
    obtain ⟨hvJ,hzv⟩ := mem_iUnion.mp hv
    let vT : {w // w ∈ T.val} := ⟨v.val,hJT hvJ⟩
    have hneF : v ≠ ⟨u.val,hTF u.property⟩ := by
      intro he; exact hu (congrArg Subtype.val he ▸ hvJ)
    have hneT : vT ≠ u := by
      intro he; exact hu (congrArg Subtype.val he ▸ hvJ)
    have heF : (⟨vT.val,hTF vT.property⟩ : {w // w ∈ F})=v := Subtype.ext rfl
    have hrv : r0 v=rT vT := by simpa only [heF] using haligned0 vT hvJ
    have hcb : Disjoint (arcInterior M (r0 v)) (arcInterior M (rT u)) := by
      rw [hrv]; exact hdT vT hvJ
    have havoid : arcInterior M (r0 v) ⊆ Hᶜ := by
      intro w hw hwH
      rcases hwH with hside | hside
      · exact disjoint_left.mp (hd0 v _ hneF) hw ⟨hfirst hside,hw.2⟩
      · exact disjoint_left.mp hcb hw ⟨hnew hside,hw.2⟩
    obtain ⟨hc,hdense⟩ := actual_bigon_arc_interior_connected_dense M (r0 v)
    have hzI : z ∈ arcInterior M (r0 v) :=
      ⟨hzv,disjoint_left.mp hmarks hzU⟩
    have heq : U=connectedComponentIn Hᶜ z := by
      exact (hU.2.2.2 _
        (isConnected_connectedComponentIn_iff.mpr (havoid hzI))
        (hU.2.1.isPreconnected.subset_connectedComponentIn hzU hU.2.2.1)
        (connectedComponentIn_subset _ _)).symm
    have hi : arcInterior M (r0 v) ⊆ U := by
      rw [heq]
      exact hc.isPreconnected.subset_connectedComponentIn hzI havoid
    have hcl : closure U ⊆ range d :=
      closure_minimal (Set.image_subset_range _ _)
        (isCompact_range d.continuous).isClosed
    have hsub : (r0 v).val.image ⊆ range d :=
      (hdense.trans (closure_mono hi)).trans hcl
    have h0 : (r0 v).val.map 0=corner :=
      hcorner _ (hsub (Set.mem_range_self _)) (r0 v).val.start_marked
    have h1 : (r0 v).val.map 1=corner :=
      hcorner _ (hsub (Set.mem_range_self _)) (r0 v).val.end_marked
    exact actual_essential_loop_not_in_interior_free_disk M (r0 v)
      (h0.trans h1.symm) d hdisk hmarks hsub
  have actual_single_mark_support_disk_boundary_contact_graph_clearance_private
      (firstSide newSide : C(Interval,S))
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hdisk : IsEmbedding d) (p q : S)
      (hmarks : Disjoint
        (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S))
      (hcorners : ∀ z ∈ range d, z ∈ M.cover.branch → z=p ∨ z=q)
      (hcontact : p ∉ M.cover.branch ∨ q ∉ M.cover.branch)
      (hboundary : d '' {x | x.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1}=range firstSide ∪ range newSide)
      (hboundaryGraph : (range firstSide ∪ range newSide) ∩ actualObjectTrace M r J ⊆
        (M.cover.branch : Set S)) :
      Disjoint (d '' {x | x.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1}) (actualObjectTrace M r J) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨corner,hcorner⟩ : ∃ corner : S,
        ∀ z ∈ range d, z ∈ M.cover.branch → z=corner := by
      rcases hcontact with hp | hq
      · refine ⟨q,?_⟩
        intro z hz hzm
        rcases hcorners z hz hzm with he | he
        · exact False.elim (hp (he ▸ hzm))
        · exact he
      · refine ⟨p,?_⟩
        intro z hz hzm
        rcases hcorners z hz hzm with he | he
        · exact he
        · exact False.elim (hq (he ▸ hzm))
    let U := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    let H := range firstSide ∪ range newSide
    have hU := actual_embedded_disk_interior_component M d hdisk
    rw [hboundary] at hU
    apply disjoint_left.mpr
    intro z hzU hzG
    rw [←hgraph] at hzG
    obtain ⟨v,hv⟩ := mem_iUnion.mp hzG
    obtain ⟨hvJ,hzv⟩ := mem_iUnion.mp hv
    have havoid : arcInterior M (r0 v) ⊆ Hᶜ := by
      intro w hw hwH
      apply hw.2
      apply hboundaryGraph
      refine ⟨hwH,?_⟩
      rw [←hgraph]
      exact mem_iUnion.mpr ⟨v,mem_iUnion.mpr ⟨hvJ,hw.1⟩⟩
    obtain ⟨hc,hdense⟩ := actual_bigon_arc_interior_connected_dense M (r0 v)
    have hzI : z ∈ arcInterior M (r0 v) :=
      ⟨hzv,disjoint_left.mp hmarks hzU⟩
    have heq : U=connectedComponentIn Hᶜ z := by
      exact (hU.2.2.2 _
        (isConnected_connectedComponentIn_iff.mpr (havoid hzI))
        (hU.2.1.isPreconnected.subset_connectedComponentIn hzU hU.2.2.1)
        (connectedComponentIn_subset _ _)).symm
    have hi : arcInterior M (r0 v) ⊆ U := by
      rw [heq]
      exact hc.isPreconnected.subset_connectedComponentIn hzI havoid
    have hcl : closure U ⊆ range d :=
      closure_minimal (Set.image_subset_range _ _)
        (isCompact_range d.continuous).isClosed
    have hsub : (r0 v).val.image ⊆ range d :=
      (hdense.trans (closure_mono hi)).trans hcl
    have h0 : (r0 v).val.map 0=corner :=
      hcorner _ (hsub (Set.mem_range_self _)) (r0 v).val.start_marked
    have h1 : (r0 v).val.map 1=corner :=
      hcorner _ (hsub (Set.mem_range_self _)) (r0 v).val.end_marked
    exact actual_essential_loop_not_in_interior_free_disk M (r0 v)
      (h0.trans h1.symm) d hdisk hmarks hsub
  have actual_essential_intrusion_produces_embedded_crosscut
      (c : EssentialMarkedArc M)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hd : IsEmbedding d)
      (hmarks : Disjoint (d '' {x | x.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1}) (M.cover.branch : Set S))
      (hin : (c.val.image ∩ (d '' {x | x.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1})).Nonempty) :
      ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ c.val.image ∧
        q 0 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
        q 1 ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} ∧
        q '' Ioo (0 : Interval) 1 ⊆
          d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    letI : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    letI : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    letI := (actualSphereSmoothAtlas M).charts
    letI := (actualSphereSmoothAtlas M).manifold
    letI : ClosedSurface S := {}
    let g : C(Interval,S) := ⟨c.val.map,c.val.continuous⟩
    have h0 : g 0 ∉ d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
      fun h => disjoint_left.mp hmarks h c.val.start_marked
    have h1 : g 1 ∉ d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} :=
      fun h => disjoint_left.mp hmarks h c.val.end_marked
    let U : Set S := d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
    let K : Set S := range d
    have hUo : IsOpen U := CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd
    have hKc : IsClosed K := (isCompact_range d.continuous).isClosed
    have hUK : U ⊆ K := image_subset_range _ _
    obtain ⟨x,⟨t,rfl⟩,htU⟩ := hin
    have htf : t ≠ 0 := by intro ht; exact h0 (ht ▸ htU)
    have htl : t ≠ 1 := by intro ht; exact h1 (ht ▸ htU)
    let L : Set Interval := Icc 0 t ∩ g ⁻¹' Uᶜ
    let R : Set Interval := Icc t 1 ∩ g ⁻¹' Uᶜ
    have hpre : IsClosed (g ⁻¹' Uᶜ) := hUo.isClosed_compl.preimage g.continuous
    have hL : L.Nonempty := ⟨0,⟨le_rfl,t.property.1⟩,h0⟩
    have hR : R.Nonempty := ⟨1,⟨t.property.2,le_rfl⟩,h1⟩
    obtain ⟨r,hr,hrmax⟩ := (isCompact_Icc.inter_right hpre).exists_isGreatest hL
    obtain ⟨s,hs,hsmin⟩ := (isCompact_Icc.inter_right hpre).exists_isLeast hR
    have hrt : r < t := lt_of_le_of_ne hr.1.2 (by intro he; exact hr.2 (he ▸ htU))
    have hts : t < s := lt_of_le_of_ne hs.1.1 (by intro he; exact hs.2 (he.symm ▸ htU))
    have hrs : r < s := hrt.trans hts
    have hinside (v : Interval) (hv : v ∈ Ioo r s) : g v ∈ U := by
      by_contra hnot
      by_cases hvt : v ≤ t
      · exact (not_lt_of_ge (hrmax ⟨⟨v.property.1,hvt⟩,hnot⟩)) hv.1
      · exact (not_lt_of_ge (hsmin ⟨⟨le_of_not_ge hvt,v.property.2⟩,hnot⟩)) hv.2
    have hIccK : Icc r s ⊆ g ⁻¹' K := by
      rw [← closure_Ioo hrs.ne]
      apply (hKc.preimage g.continuous).closure_subset_iff.mpr
      exact fun v hv => hUK (hinside v hv)
    have hboundary (v : Interval) (hvK : g v ∈ K) (hvU : g v ∉ U) :
        g v ∈ d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      obtain ⟨u,hu⟩ := hvK
      refine ⟨u,?_,hu⟩
      have hn : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hnot : ¬ ‖u.val‖ < 1 := by
        intro h
        apply hvU
        exact ⟨u,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
      simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right]
        using le_antisymm hn (le_of_not_gt hnot)
    have hginj : Set.InjOn g (Icc r s) := by
      intro v hv w hw he
      rcases c.val.injective_except_loop_closure v w he with he | ⟨hv0,hw1⟩ | ⟨hv1,hw0⟩
      · exact he
      · have hr0 : r=0 := le_antisymm (by simpa [hv0] using hv.1) r.property.1
        have hs1 : s=1 := le_antisymm s.property.2 (by simpa [hw1] using hw.2)
        have hwhole : c.val.image ⊆ range d := by
          rintro z ⟨t,rfl⟩
          exact hIccK (by rw [hr0,hs1]; exact t.property)
        have hloop : c.val.map 0=c.val.map 1 := by simpa [g,hv0,hw1] using he
        exact False.elim (actual_essential_loop_not_in_interior_free_disk M c hloop d hd hmarks hwhole)
      · have hr0 : r=0 := le_antisymm (by simpa [hw0] using hw.1) r.property.1
        have hs1 : s=1 := le_antisymm s.property.2 (by simpa [hv1] using hv.2)
        have hwhole : c.val.image ⊆ range d := by
          rintro z ⟨t,rfl⟩
          exact hIccK (by rw [hr0,hs1]; exact t.property)
        have hloop : c.val.map 0=c.val.map 1 := by simpa [g,hv1,hw0] using he.symm
        exact False.elim (actual_essential_loop_not_in_interior_free_disk M c hloop d hd hmarks hwhole)
    let affine : Interval → Interval := fun u =>
      ⟨(1-u.val)*r.val+u.val*s.val,by
        constructor <;> nlinarith [u.property.1,u.property.2,r.property.1,r.property.2,
          s.property.1,s.property.2]⟩
    have haff (u : Interval) : affine u ∈ Icc r s := by
      constructor
      · change r.val ≤ (1-u.val)*r.val+u.val*s.val
        nlinarith [u.property.1,u.property.2,show r.val < s.val from hrs]
      · change (1-u.val)*r.val+u.val*s.val ≤ s.val
        nlinarith [u.property.1,u.property.2,show r.val < s.val from hrs]
    have haffi : Function.Injective affine := by
      intro u v he
      apply Subtype.ext
      have he' := congrArg Subtype.val he
      dsimp [affine] at he'
      have hz : (u.val-v.val)*(s.val-r.val)=0 := by nlinarith only [he']
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim ((ne_of_gt (show r.val < s.val from hrs)) (sub_eq_zero.mp hz))
    let q : C(Interval,S) := ⟨g ∘ affine,g.continuous.comp (by fun_prop)⟩
    have hq0 : q 0 = g r := congrArg g (Subtype.ext (by simp [affine]))
    have hq1 : q 1 = g s := congrArg g (Subtype.ext (by simp [affine]))
    refine ⟨q,(q.continuous.isClosedEmbedding (fun u v he => haffi (hginj (haff u) (haff v) he))).isEmbedding,?_,
      hq0.symm ▸ hboundary r (hIccK ⟨le_rfl,hrs.le⟩) hr.2,
      hq1.symm ▸ hboundary s (hIccK ⟨hrs.le,le_rfl⟩) hs.2,?_⟩
    · rintro z ⟨u,rfl⟩
      exact mem_range_self (affine u)
    · rintro z ⟨u,hu,rfl⟩
      apply hinside
      constructor
      · change r.val < (1-u.val)*r.val+u.val*s.val
        nlinarith [show 0 < u.val from hu.1,show u.val < 1 from hu.2,
          show r.val < s.val from hrs]
      · change (1-u.val)*r.val+u.val*s.val < s.val
        nlinarith [show 0 < u.val from hu.1,show u.val < 1 from hu.2,
          show r.val < s.val from hrs]
  have actual_essential_subarc_interior_isOpen
      (c : EssentialMarkedArc M) (f : C(Interval,S))
      (hf : IsEmbedding f) (hfa : range f ⊆ c.val.image) :
      IsOpen {x : c.val.image | (x:S) ∈ f '' Ioo (0:Interval) 1} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let a : C(Interval,S) := ⟨c.val.map,c.val.continuous⟩
    by_cases hl : c.val.map 0=c.val.map 1
    · obtain ⟨C,hC⟩ := actual_curve_of_marked_interval_loop a hl
        c.val.injective_except_loop_closure
      have hC' : C.image=c.val.image := hC
      have hop := CurveComplex.LocalSurgery.embedded_curve_subarc_interior_isOpen
        C f hf (by simpa only [hC'] using hfa)
      exact hC' ▸ hop
    · have ha : IsEmbedding a := a.continuous.isClosedEmbedding (by
        intro t u he
        rcases c.val.injective_except_loop_closure t u he with h | h | h
        · exact h
        · have he' : c.val.map t=c.val.map u := he
          rw [h.1,h.2] at he'
          exact False.elim (hl he')
        · have he' : c.val.map t=c.val.map u := he
          rw [h.1,h.2] at he'
          exact False.elim (hl he'.symm)) |>.isEmbedding
      exact CurveComplex.LocalSurgery.embedded_interval_subarc_interior_isOpen a f ha hf hfa
  have actual_essential_intrusion_crosscut_endpoint_on_other_side
      (c : EssentialMarkedArc M) (f g q : C(Interval,S)) (hf : IsEmbedding f)
      (hfa : range f ⊆ c.val.image) (hqa : range q ⊆ c.val.image)
      (hf0 : f 0=g 0) (hf1 : f 1=g 1)
      (U : Set S) (hfree : Disjoint U (range f ∪ range g))
      (hqin : q '' Ioo (0:Interval) 1 ⊆ U)
      (e : Interval) (hqe : q e ∈ range f ∪ range g) : q e ∈ range g := by
    by_contra hnot
    have hefirst : q e ∈ range f := hqe.resolve_right hnot
    obtain ⟨v,hv⟩ := hefirst
    have hv0 : v ≠ 0 := by
      intro h
      exact hnot ⟨0,hf0.symm.trans ((congrArg f h).symm.trans hv)⟩
    have hv1 : v ≠ 1 := by
      intro h
      exact hnot ⟨1,hf1.symm.trans ((congrArg f h).symm.trans hv)⟩
    have hvI : v ∈ Ioo (0:Interval) 1 :=
      ⟨lt_of_le_of_ne v.property.1 (Ne.symm hv0),lt_of_le_of_ne v.property.2 hv1⟩
    let qa : C(Interval,c.val.image) := ⟨fun t => ⟨q t,hqa (mem_range_self t)⟩,
      q.continuous.subtype_mk _⟩
    let V : Set Interval := qa ⁻¹' {x : c.val.image | (x:S) ∈ f '' Ioo (0:Interval) 1}
    have hVo : IsOpen V := (actual_essential_subarc_interior_isOpen c f hf hfa).preimage
      qa.continuous
    have heV : e ∈ V := ⟨v,hvI,hv⟩
    have hecl : e ∈ closure (Ioo (0:Interval) 1) := by
      rw [closure_Ioo (by norm_num : (0:Interval) ≠ 1)]
      exact e.property
    obtain ⟨t,htV,htI⟩ := mem_closure_iff_nhds.mp hecl V (hVo.mem_nhds heV)
    have htU : q t ∈ U := hqin (mem_image_of_mem q htI)
    obtain ⟨w,hwI,hw⟩ := htV
    exact Set.disjoint_left.mp hfree htU (Or.inl ⟨w,hw⟩)
  have actual_selected_disk_intrusion_crosscut_other_side
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hin : (a.val.image ∩ B.openInterior).Nonempty) :
      ∃ q : C(Interval,S), IsEmbedding q ∧ range q ⊆ a.val.image ∧
        q 0 ∈ range B.secondSide ∧ q 1 ∈ range B.secondSide ∧
        q '' Ioo (0:Interval) 1 ⊆ B.openInterior := by
    let : T2Space S := M.sphere.symm.t2Space
    let : CompactSpace S := M.sphere.symm.compactSpace
    let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    let := (actualSphereSmoothAtlas M).charts
    let := (actualSphereSmoothAtlas M).manifold
    let : ClosedSurface S := {}
    have hbranch : Disjoint B.openInterior (M.cover.branch : Set S) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ hxmark
      have hxc : x ∈ ({B.firstCorner,B.secondCorner}:Set S) :=
        B.marks_are_corners x ⟨u,hux⟩ hxmark
      have hxboundary : x ∈ B.disk ''
          {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [B.boundary_eq]
        left
        rcases Set.mem_insert_iff.mp hxc with hx | hx
        · exact ⟨0,B.first_zero.trans hx.symm⟩
        · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp hx).symm⟩
      obtain ⟨v,hv,hvx⟩ := hxboundary
      have huv : u = v := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    obtain ⟨q,hq,hqa,hq0,hq1,hqin⟩ :=
      actual_essential_intrusion_produces_embedded_crosscut a B.disk B.disk_embedded hbranch hin
    have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
      rw [← B.boundary_eq]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    have hqe (e : Interval) (he : q e ∈ range B.firstSide ∪ range B.secondSide) :
        q e ∈ range B.secondSide :=
      actual_essential_intrusion_crosscut_endpoint_on_other_side
        a B.firstSide B.secondSide q B.first_embedded B.first_on_curve hqa
        (B.first_zero.trans B.second_zero.symm) (B.first_one.trans B.second_one.symm)
        B.openInterior hfree hqin e he
    refine ⟨q,hq,hqa,hqe 0 (B.boundary_eq ▸ hq0),hqe 1 (B.boundary_eq ▸ hq1),hqin⟩
  have actual_selected_intrusion_crosscut_produces_smaller_disk
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hbranch : Disjoint B.openInterior (M.cover.branch : Set S))
      (q : C(Interval,S)) (hq : IsEmbedding q) (hqa : range q ⊆ a.val.image)
      (hq0 : q 0 ∈ range B.secondSide) (hq1 : q 1 ∈ range B.secondSide)
      (hqin : q '' Ioo (0:Interval) 1 ⊆ B.openInterior)
      (hnotboth : ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S))) :
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S),x ∉ range D.disk) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) := by
    classical
    let : T2Space S := M.sphere.symm.t2Space
    let : CompactSpace S := M.sphere.symm.compactSpace
    let : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      Subtype.connectedSpace (isConnected_sphere
        (by simp only [← Module.finrank_eq_rank,finrank_euclideanSpace_fin]; norm_num)
        0 (by norm_num))
    let : ConnectedSpace S := M.sphere.symm.surjective.connectedSpace M.sphere.symm.continuous
    let := (actualSphereSmoothAtlas M).charts
    let := (actualSphereSmoothAtlas M).manifold
    let : ClosedSurface S := {}
    have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
      rw [← B.boundary_eq]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    obtain ⟨r,hr⟩ := hq0
    obtain ⟨s,hs⟩ := hq1
    have hrs : r ≠ s := by
      intro he
      have h01 : (0:Interval) = 1 := hq.injective (hr.symm.trans ((congrArg B.secondSide he).trans hs))
      exact zero_ne_one h01
    let affine : Interval → Interval := fun t =>
      ⟨(1-t.val)*r.val+t.val*s.val,by
        constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
          s.property.1,s.property.2]⟩
    let g : C(Interval,S) := ⟨B.secondSide ∘ affine,B.secondSide.continuous.comp (by fun_prop)⟩
    have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
    have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
    have hgi : Function.Injective g := by
      intro t u he
      have hv := congrArg Subtype.val (B.second_embedded.injective he)
      apply Subtype.ext
      have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
      dsimp [affine] at hv
      have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
      rcases mul_eq_zero.mp hz with hz | hz
      · exact sub_eq_zero.mp hz
      · exact False.elim (hne (sub_eq_zero.mp hz).symm)
    have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
    have hgg : range g ⊆ range B.secondSide := by
      rintro x ⟨t,rfl⟩
      exact mem_range_self (affine t)
    have hcross (t u : Interval) (he : q t = g u) :
        (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
      by_cases ht0 : t=0
      · exact Or.inl ⟨ht0,hgi (by rw [hg0,← he,ht0])⟩
      by_cases ht1 : t=1
      · exact Or.inr ⟨ht1,hgi (by rw [hg1,← he,ht1])⟩
      have htI : t ∈ Ioo (0:Interval) 1 :=
        ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
      exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
        (Or.inr (he.symm ▸ hgg (mem_range_self u))))
    obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hgi hg0.symm hg1.symm hcross
    have hcB : c.image ⊆ range B.disk := by
      rw [hc]
      apply union_subset
      · rintro x ⟨t,rfl⟩
        by_cases ht0 : t=0
        · subst t
          exact image_subset_range _ _ (B.boundary_eq.symm ▸
            (show q 0 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨r,hr⟩))
        by_cases ht1 : t=1
        · subst t
          exact image_subset_range _ _ (B.boundary_eq.symm ▸
            (show q 1 ∈ range B.firstSide ∪ range B.secondSide from Or.inr ⟨s,hs⟩))
        exact image_subset_range _ _ (hqin ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
      · exact fun x hx => image_subset_range _ _ (B.boundary_eq.symm ▸
          (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inr (hgg hx)))
    obtain ⟨d,hd,hdb,hdB⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk
      c B.disk B.disk_embedded hcB
    have hdin : d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆ B.openInterior := by
      change d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1} ⊆
        B.disk '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}
      rw [← CurveComplex.LocalSurgery.embedded_surface_disk_interior_eq B.disk B.disk_embedded]
      exact (CurveComplex.LocalSurgery.embedded_surface_disk_interior_isOpen d hd).subset_interior_iff.mpr
        ((image_subset_range _ _).trans hdB)
    have hmarks : ∀ x ∈ range d, x ∈ M.cover.branch → x ∈ ({q 0,q 1}:Set S) := by
      intro x hx hxmark
      obtain ⟨u,hu⟩ := hx
      have hnorm : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hne : ¬ ‖u.val‖ < 1 := by
        intro h
        have hxU := hdin ⟨u,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using h,hu⟩
        exact Set.disjoint_left.mp hbranch hxU hxmark
      have hxc : x ∈ c.image := hdb ▸ (show x ∈ d ''
          {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} from
        ⟨u,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right]
          using le_antisymm hnorm (not_lt.mp hne),hu⟩)
      rw [hc] at hxc
      rcases hxc with ⟨t,ht⟩ | ⟨t,ht⟩
      · have htend : t=0 ∨ t=1 := by
          by_cases ht0 : t=0
          · exact Or.inl ht0
          by_cases ht1 : t=1
          · exact Or.inr ht1
          have hti : t ∈ Ioo (0:Interval) 1 :=
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
          exact False.elim (Set.disjoint_left.mp hbranch (hqin ⟨t,hti,rfl⟩) (ht.symm ▸ hxmark))
        rcases htend with ht0 | ht1
        · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
      · have hxB : x ∈ range B.disk := hdB ⟨u,hu⟩
        have hcorn := B.marks_are_corners x hxB hxmark
        have he : g t=B.secondSide 0 ∨ g t=B.secondSide 1 := by
          rcases mem_insert_iff.mp hcorn with hc0 | hc1
          · exact Or.inl (ht.trans (hc0.trans B.second_zero.symm))
          · exact Or.inr (ht.trans ((mem_singleton_iff.mp hc1).trans B.second_one.symm))
        rcases actual_embedded_side_source_endpoint B.secondSide g B.second_embedded hg hgg t he with ht0 | ht1
        · exact Or.inl ((hg0.symm.trans ((congrArg g ht0).symm.trans ht))).symm
        · exact Or.inr ((hg1.symm.trans ((congrArg g ht1).symm.trans ht))).symm
    have hsides : range q ∩ range g = {q 0,q 1} := by
      ext x
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        rcases hcross t u (ht.trans hu.symm) with ⟨ht0,_⟩ | ⟨ht1,_⟩
        · exact Or.inl ((congrArg q ht0).symm.trans ht).symm
        · exact Or.inr ((congrArg q ht1).symm.trans ht).symm
      · intro hx
        rcases mem_insert_iff.mp hx with hx | hx
        · exact hx ▸ ⟨⟨0,rfl⟩,⟨0,hg0⟩⟩
        · exact mem_singleton_iff.mp hx ▸ ⟨⟨1,rfl⟩,⟨1,hg1⟩⟩
    let D : ActualMarkedTwoSideDisk M a b := {
      firstCorner := q 0, secondCorner := q 1,
      firstSide := q, secondSide := g, first_embedded := hq, second_embedded := hg,
      first_zero := rfl,first_one := rfl,second_zero := hg0,second_one := hg1,
      first_on_curve := hqa, second_on_curve := hgg.trans B.second_on_curve,
      sides_inter := hsides,disk := d,disk_embedded := hd,boundary_eq := hdb.trans hc,
      marks_are_corners := hmarks }
    have hmissing : ∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S), x ∉ range D.disk := by
      have hn01 : ¬ (r=0 ∧ s=1) := by
        rintro ⟨rfl,rfl⟩
        apply hnotboth
        rw [← hr,← hs,B.second_zero,B.second_one]
        exact ⟨Or.inl rfl,Or.inr rfl⟩
      have hn10 : ¬ (r=1 ∧ s=0) := by
        rintro ⟨rfl,rfl⟩
        apply hnotboth
        rw [← hr,← hs,B.second_one,B.second_zero]
        exact ⟨Or.inr rfl,Or.inl rfl⟩
      have hend : ∃ v : Interval, (v=0 ∨ v=1) ∧ r≠v ∧ s≠v := by
        by_cases hr0 : r=0
        · refine ⟨1,Or.inr rfl,?_,fun hs1 => hn01 ⟨hr0,hs1⟩⟩
          rw [hr0]
          exact zero_ne_one
        by_cases hs0 : s=0
        · refine ⟨1,Or.inr rfl,fun hr1 => hn10 ⟨hr1,hs0⟩,?_⟩
          rw [hs0]
          exact zero_ne_one
        exact ⟨0,Or.inl rfl,hr0,hs0⟩
      obtain ⟨v,hv,hrv,hsv⟩ := hend
      let x : S := B.secondSide v
      have hxcorner : x ∈ ({B.firstCorner,B.secondCorner}:Set S) := by
        rcases hv with hv | hv
        · exact Or.inl ((congrArg B.secondSide hv).trans B.second_zero)
        · exact Or.inr ((congrArg B.secondSide hv).trans B.second_one)
      have hxB : x ∈ range B.firstSide ∪ range B.secondSide := Or.inr (mem_range_self v)
      have hxnotq : x ∉ range q := by
        rintro ⟨t,ht⟩
        by_cases ht0 : t=0
        · apply hrv
          apply B.second_embedded.injective
          exact hr.trans ((congrArg q ht0).symm.trans ht)
        by_cases ht1 : t=1
        · apply hsv
          apply B.second_embedded.injective
          exact hs.trans ((congrArg q ht1).symm.trans ht)
        exact Set.disjoint_left.mp hfree (ht ▸ hqin ⟨t,
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩) hxB
      have hxnotg : x ∉ range g := by
        rintro ⟨t,ht⟩
        have he : g t = B.secondSide 0 ∨ g t = B.secondSide 1 := by
          rcases hv with hv | hv
          · exact Or.inl (ht.trans (congrArg B.secondSide hv))
          · exact Or.inr (ht.trans (congrArg B.secondSide hv))
        rcases actual_embedded_side_source_endpoint B.secondSide g B.second_embedded hg hgg t he
          with ht0 | ht1
        · exact hxnotq ⟨0,hg0.symm.trans ((congrArg g ht0).symm.trans ht)⟩
        · exact hxnotq ⟨1,hg1.symm.trans ((congrArg g ht1).symm.trans ht)⟩
      have hxnotc : x ∉ c.image := by
        rw [hc]
        exact fun h => h.elim hxnotq hxnotg
      refine ⟨x,hxcorner,?_⟩
      rintro ⟨u,hu⟩
      have hnorm : ‖u.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using u.property
      have hne : ‖u.val‖ ≠ 1 := by
        intro he
        apply hxnotc
        rw [← hdb]
        exact ⟨u,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using he,hu⟩
      have hxinside : x ∈ B.openInterior := hdin ⟨u,
        by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right]
          using lt_of_le_of_ne hnorm hne,hu⟩
      exact Set.disjoint_left.mp hfree hxinside hxB
    have hcontact : D.firstCorner ∈ ArcSurgery.crossings M a b ∨
        D.secondCorner ∈ ArcSurgery.crossings M a b := by
      by_cases h0mark : q 0 ∈ M.cover.branch
      · right
        have h1not : q 1 ∉ M.cover.branch := by
          intro h1mark
          exact hnotboth ⟨B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 0))) h0mark,
            B.marks_are_corners _ (hcB (hc.symm ▸ Or.inl (mem_range_self 1))) h1mark⟩
        exact ⟨⟨hqa (mem_range_self 1),h1not⟩,B.second_on_curve ⟨s,hs⟩,h1not⟩
      · left
        exact ⟨⟨hqa (mem_range_self 0),h0mark⟩,B.second_on_curve ⟨r,hr⟩,h0mark⟩
    exact ⟨D,hdB,hmissing,hcontact⟩
  have actual_selected_intrusion_crosscut_not_both_corners
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hbranch : Disjoint B.openInterior (M.cover.branch : Set S))
      (q : C(Interval,S)) (hq : IsEmbedding q) (hqa : range q ⊆ a.val.image)
      (hqin : q '' Ioo (0:Interval) 1 ⊆ B.openInterior) :
      ¬ (q 0 ∈ ({B.firstCorner,B.secondCorner}:Set S) ∧
        q 1 ∈ ({B.firstCorner,B.secondCorner}:Set S)) := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    rintro ⟨hc0,hc1⟩
    have hcorner (x : S) (hx : x ∈ ({B.firstCorner,B.secondCorner}:Set S)) :
        x ∈ range B.firstSide := by
      rcases mem_insert_iff.mp hx with hx | hx
      · exact ⟨0,B.first_zero.trans hx.symm⟩
      · exact ⟨1,B.first_one.trans (mem_singleton_iff.mp hx).symm⟩
    have hq0 := hcorner _ hc0
    have hq1 := hcorner _ hc1
    have hfree : Disjoint B.openInterior (range B.firstSide ∪ range B.secondSide) := by
      rw [← B.boundary_eq]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv := B.disk_embedded.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
    by_cases hloop : a.val.map 0=a.val.map 1
    · obtain ⟨C,hC⟩ := actual_curve_of_marked_interval_loop A hloop
        a.val.injective_except_loop_closure
      obtain ⟨r,hr⟩ := hq0
      obtain ⟨s,hs⟩ := hq1
      have hrs : r ≠ s := by
        intro he
        have h01 : (0:Interval) = 1 := hq.injective (hr.symm.trans ((congrArg B.firstSide he).trans hs))
        exact zero_ne_one h01
      let affine : Interval → Interval := fun t =>
        ⟨(1-t.val)*r.val+t.val*s.val,by
          constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
            s.property.1,s.property.2]⟩
      let g : C(Interval,S) := ⟨B.firstSide ∘ affine,B.firstSide.continuous.comp (by fun_prop)⟩
      have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
      have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
      have hgi : Function.Injective g := by
        intro t u he
        have hv := congrArg Subtype.val (B.first_embedded.injective he)
        apply Subtype.ext
        have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
        dsimp [affine] at hv
        have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
        rcases mul_eq_zero.mp hz with hz | hz
        · exact sub_eq_zero.mp hz
        · exact False.elim (hne (sub_eq_zero.mp hz).symm)
      have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
      have hgf : range g ⊆ range B.firstSide := by
        rintro x ⟨t,rfl⟩
        exact mem_range_self (affine t)
      have hcross (t u : Interval) (he : q t = g u) :
          (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
        by_cases ht0 : t=0
        · exact Or.inl ⟨ht0,hgi (by rw [hg0,← he,ht0])⟩
        by_cases ht1 : t=1
        · exact Or.inr ⟨ht1,hgi (by rw [hg1,← he,ht1])⟩
        have htI : t ∈ Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
          (Or.inl (he.symm ▸ hgf (mem_range_self u))))
      obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hgi hg0.symm hg1.symm hcross
      have hcB : c.image ⊆ range B.disk := by
        rw [hc]
        apply union_subset
        · rintro x ⟨t,rfl⟩
          by_cases ht0 : t=0
          · subst t
            exact image_subset_range _ _ (B.boundary_eq.symm ▸
              (show q 0 ∈ range B.firstSide ∪ range B.secondSide from Or.inl ⟨r,hr⟩))
          by_cases ht1 : t=1
          · subst t
            exact image_subset_range _ _ (B.boundary_eq.symm ▸
              (show q 1 ∈ range B.firstSide ∪ range B.secondSide from Or.inl ⟨s,hs⟩))
          exact image_subset_range _ _ (hqin ⟨t,
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
        · exact fun x hx => image_subset_range _ _ (B.boundary_eq.symm ▸
            (show x ∈ range B.firstSide ∪ range B.secondSide from Or.inl (hgf hx)))
      have hcC : c.image ⊆ C.image := by
        rw [hC,hc]
        exact union_subset hqa (hgf.trans B.first_on_curve)
      have hwhole : a.val.image ⊆ range B.disk := by
        have heq := CurveComplex.LocalSurgery.curve_image_eq_of_subset C c hcC
        have hC' : C.image=a.val.image := hC
        rw [hC'] at heq
        exact heq ▸ hcB
      exact actual_essential_loop_not_in_interior_free_disk M a hloop
        B.disk B.disk_embedded hbranch hwhole
    · have hAi : Function.Injective A := by
        intro t u he
        rcases a.val.injective_except_loop_closure t u he with ht | ht | ht
        · exact ht
        · have he' : a.val.map t=a.val.map u := he
          rw [ht.1,ht.2] at he'
          exact False.elim (hloop he')
        · have he' : a.val.map t=a.val.map u := he
          rw [ht.1,ht.2] at he'
          exact False.elim (hloop he'.symm)
      have hA : IsEmbedding A := A.continuous.isClosedEmbedding hAi |>.isEmbedding
      have hqf : range q ⊆ range B.firstSide :=
        CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
          A B.firstSide q hA hq B.first_on_curve hqa hq0 hq1
      let t : Interval := ⟨1/2,by constructor <;> norm_num⟩
      have ht : t ∈ Ioo (0:Interval) 1 := by
        constructor
        · change (0:ℝ)<1/2; norm_num
        · change (1/2:ℝ)<1; norm_num
      exact Set.disjoint_left.mp hfree (hqin (mem_image_of_mem q ht))
        (Or.inl (hqf (mem_range_self t)))
  have actual_essential_source_crosscut_cannot_return_to_same_embedded_core_private
      (a : EssentialMarkedArc M) (f otherSide : C(Interval,S))
      (hf : IsEmbedding f) (hfa : range f ⊆ a.val.image)
      (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
      (hboundary : d '' {x | x.val ∈ Metric.sphere (0:Plane) 1}=range f ∪ range otherSide)
      (hbranch : Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (M.cover.branch:Set S))
      (q : C(Interval,S)) (hq : IsEmbedding q) (hqa : range q ⊆ a.val.image)
      (hqin : q '' Ioo (0:Interval) 1 ⊆ d '' {x | x.val ∈ Metric.ball (0:Plane) 1})
      (hq0 : q 0 ∈ range f) (hq1 : q 1 ∈ range f) : False := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hfree : Disjoint (d '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) (range f ∪ range otherSide) := by
      rw [← hboundary]
      apply Set.disjoint_left.mpr
      rintro x ⟨u,hu,hux⟩ ⟨v,hv,hvx⟩
      have huv := hd.injective (hux.trans hvx.symm)
      subst v
      have hu' : ‖u.val‖ < 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
      have hv' : ‖u.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
      linarith
    let A : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
    by_cases hloop : a.val.map 0=a.val.map 1
    · obtain ⟨C,hC⟩ := actual_curve_of_marked_interval_loop A hloop
        a.val.injective_except_loop_closure
      obtain ⟨r,hr⟩ := hq0
      obtain ⟨s,hs⟩ := hq1
      have hrs : r ≠ s := by
        intro he
        have h01 : (0:Interval) = 1 := hq.injective (hr.symm.trans ((congrArg f he).trans hs))
        exact zero_ne_one h01
      let affine : Interval → Interval := fun t =>
        ⟨(1-t.val)*r.val+t.val*s.val,by
          constructor <;> nlinarith [t.property.1,t.property.2,r.property.1,r.property.2,
            s.property.1,s.property.2]⟩
      let g : C(Interval,S) := ⟨f ∘ affine,f.continuous.comp (by fun_prop)⟩
      have hg0 : g 0 = q 0 := by simpa [g,affine] using hr
      have hg1 : g 1 = q 1 := by simpa [g,affine] using hs
      have hgi : Function.Injective g := by
        intro t u he
        have hv := congrArg Subtype.val (hf.injective he)
        apply Subtype.ext
        have hne : r.val ≠ s.val := fun he => hrs (Subtype.ext he)
        dsimp [affine] at hv
        have hz : (t.val-u.val)*(s.val-r.val)=0 := by nlinarith only [hv]
        rcases mul_eq_zero.mp hz with hz | hz
        · exact sub_eq_zero.mp hz
        · exact False.elim (hne (sub_eq_zero.mp hz).symm)
      have hg : IsEmbedding g := (g.continuous.isClosedEmbedding hgi).isEmbedding
      have hgf : range g ⊆ range f := by
        rintro x ⟨t,rfl⟩
        exact mem_range_self (affine t)
      have hcross (t u : Interval) (he : q t = g u) :
          (t=0 ∧ u=0) ∨ (t=1 ∧ u=1) := by
        by_cases ht0 : t=0
        · exact Or.inl ⟨ht0,hgi (by rw [hg0,← he,ht0])⟩
        by_cases ht1 : t=1
        · exact Or.inr ⟨ht1,hgi (by rw [hg1,← he,ht1])⟩
        have htI : t ∈ Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩
        exact False.elim (Set.disjoint_left.mp hfree (hqin ⟨t,htI,rfl⟩)
          (Or.inl (he.symm ▸ hgf (mem_range_self u))))
      obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs q g hq.injective hgi hg0.symm hg1.symm hcross
      have hcB : c.image ⊆ range d := by
        rw [hc]
        apply union_subset
        · rintro x ⟨t,rfl⟩
          by_cases ht0 : t=0
          · subst t
            exact image_subset_range _ _ (hboundary.symm ▸
              (show q 0 ∈ range f ∪ range otherSide from Or.inl ⟨r,hr⟩))
          by_cases ht1 : t=1
          · subst t
            exact image_subset_range _ _ (hboundary.symm ▸
              (show q 1 ∈ range f ∪ range otherSide from Or.inl ⟨s,hs⟩))
          exact image_subset_range _ _ (hqin ⟨t,
            ⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩)
        · exact fun x hx => image_subset_range _ _ (hboundary.symm ▸
            (show x ∈ range f ∪ range otherSide from Or.inl (hgf hx)))
      have hcC : c.image ⊆ C.image := by
        rw [hC,hc]
        exact union_subset hqa (hgf.trans hfa)
      have hwhole : a.val.image ⊆ range d := by
        have heq := CurveComplex.LocalSurgery.curve_image_eq_of_subset C c hcC
        have hC' : C.image=a.val.image := hC
        rw [hC'] at heq
        exact heq ▸ hcB
      exact actual_essential_loop_not_in_interior_free_disk M a hloop
        d hd hbranch hwhole
    · have hAi : Function.Injective A := by
        intro t u he
        rcases a.val.injective_except_loop_closure t u he with ht | ht | ht
        · exact ht
        · have he' : a.val.map t=a.val.map u := he
          rw [ht.1,ht.2] at he'
          exact False.elim (hloop he')
        · have he' : a.val.map t=a.val.map u := he
          rw [ht.1,ht.2] at he'
          exact False.elim (hloop he'.symm)
      have hA : IsEmbedding A := A.continuous.isClosedEmbedding hAi |>.isEmbedding
      have hqf : range q ⊆ range f :=
        CurveComplex.LocalSurgery.embedded_interval_subarc_subset_of_endpoints_mem
          A f q hA hq hfa hqa hq0 hq1
      let t : Interval := ⟨1/2,by constructor <;> norm_num⟩
      have ht : t ∈ Ioo (0:Interval) 1 := by
        constructor
        · change (0:ℝ)<1/2; norm_num
        · change (1/2:ℝ)<1; norm_num
      exact Set.disjoint_left.mp hfree (hqin (mem_image_of_mem q ht))
        (Or.inl (hqf (mem_range_self t)))
  have actual_single_mark_support_disk_entire_old_core_carrier_exterior_private
      (b : EssentialMarkedArc M) (c g : C(Interval,S))
      (hc : IsEmbedding c) (hcb : range c ⊆ b.val.image)
      (hc0 : c 0=g 0) (hc1 : c 1=g 1)
      (hgB : range g ∩ b.val.image={g 0,g 1})
      (d : C(Metric.closedBall (0:Plane) 1,S)) (hd : IsEmbedding d)
      (hboundary : d '' {x | x.val ∈ Metric.sphere (0:Plane) 1}=range c ∪ range g)
      (hmarks : Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (M.cover.branch:Set S)) :
      Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) b.val.image := by
    apply disjoint_left.mpr
    intro z hzD hzB
    obtain ⟨q,hq,hqb,hq0,hq1,hqin⟩ := actual_essential_intrusion_produces_embedded_crosscut
      b d hd hmarks ⟨z,hzB,hzD⟩
    have hfree : Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (range c ∪ range g) := by
      rw [←hboundary]
      apply disjoint_left.mpr
      rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
      have hxy := hd.injective (hxz.trans hyz.symm)
      subst y
      have hx' : ‖x.val‖<1 := by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hx
      have hy' : ‖x.val‖=1 := by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hy
      linarith
    have hport (e : Interval) (he : q e ∈ range c ∪ range g) : q e ∈ range c := by
      have hqg := actual_essential_intrusion_crosscut_endpoint_on_other_side
        b c g q hc hcb hqb hc0 hc1
        (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) hfree hqin e he
      have hh : q e ∈ ({g 0,g 1}:Set S) := hgB ▸ ⟨hqg,hqb (mem_range_self e)⟩
      rcases mem_insert_iff.mp hh with hh | hh
      · exact ⟨0,hc0.trans hh.symm⟩
      · exact ⟨1,hc1.trans (mem_singleton_iff.mp hh).symm⟩
    exact actual_essential_source_crosscut_cannot_return_to_same_embedded_core_private
      b c g hc hcb d hd hboundary hmarks q hq hqb hqin
      (hport 0 (hboundary ▸ hq0)) (hport 1 (hboundary ▸ hq1))
  have actual_selected_disk_interior_mark_free
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b) :
      Disjoint B.openInterior (M.cover.branch : Set S) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨u,hu,hux⟩ hxmark
    have hxc : x ∈ ({B.firstCorner,B.secondCorner}:Set S) :=
      B.marks_are_corners x ⟨u,hux⟩ hxmark
    have hxboundary : x ∈ B.disk ''
        {v | v.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
      rw [B.boundary_eq]
      left
      rcases Set.mem_insert_iff.mp hxc with hx | hx
      · exact ⟨0,B.first_zero.trans hx.symm⟩
      · exact ⟨1,B.first_one.trans (Set.mem_singleton_iff.mp hx).symm⟩
    obtain ⟨v,hv,hvx⟩ := hxboundary
    have huv : u = v := B.disk_embedded.injective (hux.trans hvx.symm)
    subst v
    have hu' : ‖u.val‖ < 1 := by
      simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hu
    have hv' : ‖u.val‖ = 1 := by
      simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hv
    linarith
  have actual_first_intrusion_strictly_smaller_disk
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hin : (a.val.image ∩ B.openInterior).Nonempty) :
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S),x ∉ range D.disk) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) := by
    obtain ⟨q,hq,hqa,hq0,hq1,hqin⟩ :=
      actual_selected_disk_intrusion_crosscut_other_side a b B hin
    have hbranch := actual_selected_disk_interior_mark_free a b B
    have hnotboth := actual_selected_intrusion_crosscut_not_both_corners
      a b B hbranch q hq hqa hqin
    exact actual_selected_intrusion_crosscut_produces_smaller_disk
      a b B hbranch q hq hqa hq0 hq1 hqin hnotboth
  have actual_either_intrusion_strictly_smaller_disk
      (a b : EssentialMarkedArc M) (B : ActualMarkedTwoSideDisk M a b)
      (hin : ((a.val.image ∪ b.val.image) ∩ B.openInterior).Nonempty) :
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        (∃ x ∈ ({B.firstCorner,B.secondCorner}:Set S),x ∉ range D.disk) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) := by
    obtain ⟨x,hxa | hxb,hxB⟩ := hin
    · exact actual_first_intrusion_strictly_smaller_disk a b B ⟨x,hxa,hxB⟩
    · let swap {c d : EssentialMarkedArc M} (K : ActualMarkedTwoSideDisk M c d) :
          ActualMarkedTwoSideDisk M d c := {
        firstCorner := K.firstCorner,secondCorner := K.secondCorner,
        firstSide := K.secondSide,secondSide := K.firstSide,
        first_embedded := K.second_embedded,second_embedded := K.first_embedded,
        first_zero := K.second_zero,first_one := K.second_one,
        second_zero := K.first_zero,second_one := K.first_one,
        first_on_curve := K.second_on_curve,second_on_curve := K.first_on_curve,
        sides_inter := by rw [Set.inter_comm,K.sides_inter],
        disk := K.disk,disk_embedded := K.disk_embedded,
        boundary_eq := K.boundary_eq.trans (Set.union_comm _ _),
        marks_are_corners := K.marks_are_corners }
      obtain ⟨D,hsub,hmissing,hcontact⟩ :=
        actual_first_intrusion_strictly_smaller_disk b a (swap B) ⟨x,hxb,hxB⟩
      refine ⟨swap D,hsub,hmissing,?_⟩
      simpa only [ArcSurgery.crossings,Set.inter_comm] using hcontact
  have actual_initial_contact_disk_produces_entire_pair_clearance
      (a b : EssentialMarkedArc M)
      (hfinite : (ArcSurgery.crossings M a b).Finite)
      (B : ActualMarkedTwoSideDisk M a b)
      (hcontact : B.firstCorner ∈ ArcSurgery.crossings M a b ∨
        B.secondCorner ∈ ArcSurgery.crossings M a b) :
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        Disjoint D.openInterior (a.val.image ∪ b.val.image ∪ (M.cover.branch : Set S)) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) ∧
        (∀ x ∈ ({a.val.map 0,a.val.map 1}:Set S),
          x ≠ D.firstCorner → x ≠ D.secondCorner → x ∉ range D.disk) := by
    classical
    let C : Set S := a.val.image ∩ b.val.image
    have hCf : C.Finite :=
      (hfinite.union (Set.toFinite ({a.val.map 0,a.val.map 1}:Set S))).subset (by
        intro x hx
        by_cases hxmark : x ∈ M.cover.branch
        · right
          obtain ⟨t,ht⟩ := hx.1
          rcases a.val.marked_only_at_ends t (ht ▸ hxmark) with ht0 | ht1
          · exact Or.inl ((congrArg a.val.map ht0).symm.trans ht).symm
          · exact Or.inr ((congrArg a.val.map ht1).symm.trans ht).symm
        · exact Or.inl ⟨⟨hx.1,hxmark⟩,hx.2,hxmark⟩)
    let energy (D : ActualMarkedTwoSideDisk M a b) : ℕ :=
      (C ∩ range D.disk).ncard
    let P : ℕ → Prop := fun n =>
      ∃ D : ActualMarkedTwoSideDisk M a b,
        range D.disk ⊆ range B.disk ∧
        (D.firstCorner ∈ ArcSurgery.crossings M a b ∨
          D.secondCorner ∈ ArcSurgery.crossings M a b) ∧ energy D = n
    have hex : ∃ n,P n := ⟨energy B,B,Subset.rfl,hcontact,rfl⟩
    obtain ⟨D,hDB,hDcontact,hDenergy⟩ := Nat.find_spec hex
    have hempty : Disjoint D.openInterior (a.val.image ∪ b.val.image) := by
      apply Set.disjoint_left.mpr
      intro x hxDisk hxArc
      obtain ⟨F,hFD,⟨z,hzcorner,hznotF⟩,hFcontact⟩ :=
        actual_either_intrusion_strictly_smaller_disk a b D ⟨x,hxArc,hxDisk⟩
      have hzC : z ∈ C := by
        rcases mem_insert_iff.mp hzcorner with hz | hz
        · exact ⟨D.first_on_curve ⟨0,D.first_zero.trans hz.symm⟩,
            D.second_on_curve ⟨0,D.second_zero.trans hz.symm⟩⟩
        · have hz' := mem_singleton_iff.mp hz
          exact ⟨D.first_on_curve ⟨1,D.first_one.trans hz'.symm⟩,
            D.second_on_curve ⟨1,D.second_one.trans hz'.symm⟩⟩
      have hzD : z ∈ range D.disk := image_subset_range _ _ (D.boundary_eq.symm ▸
        (show z ∈ range D.firstSide ∪ range D.secondSide from
          Or.inl (by
            rcases mem_insert_iff.mp hzcorner with hz | hz
            · exact ⟨0,D.first_zero.trans hz.symm⟩
            · exact ⟨1,D.first_one.trans (mem_singleton_iff.mp hz).symm⟩)))
      have hlt : energy F < energy D := Set.ncard_lt_ncard
        (Set.ssubset_iff_subset_ne.mpr ⟨Set.inter_subset_inter_right C hFD,by
          intro he
          have hzF : z ∈ C ∩ range F.disk := he.symm ▸ (show z ∈ C ∩ range D.disk from ⟨hzC,hzD⟩)
          exact hznotF hzF.2⟩) (hCf.inter_of_left _)
      exact Nat.find_min hex (hlt.trans_eq hDenergy)
        ⟨F,hFD.trans hDB,hFcontact,rfl⟩
    refine ⟨D,hDB,hempty.union_right (actual_selected_disk_interior_mark_free a b D),hDcontact,?_⟩
    intro x hx hxfirst hxsecond hxdisk
    have hxmark : x ∈ M.cover.branch := by
      rcases mem_insert_iff.mp hx with hx | hx
      · exact hx ▸ a.val.start_marked
      · exact mem_singleton_iff.mp hx ▸ a.val.end_marked
    rcases mem_insert_iff.mp (D.marks_are_corners x hxdisk hxmark) with hx | hx
    · exact hxfirst hx
    · exact hxsecond (mem_singleton_iff.mp hx)
  letI : T2Space S := M.sphere.symm.t2Space
  obtain ⟨B,hBcontact⟩ := hInitial
  obtain ⟨D,hDB,hDfree,hDcontact,hDends⟩ :=
    actual_initial_contact_disk_produces_entire_pair_clearance
      (r0 ⟨u.val,hTF u.property⟩) (rT u) hfinite B hBcontact
  have hDmark := actual_selected_disk_interior_mark_free _ _ D
  have hpositive : D.firstCorner∉M.cover.branch ∨ D.secondCorner∉M.cover.branch := by
    rcases hDcontact with hc | hc
    · exact Or.inl hc.1.2
    · exact Or.inr hc.1.2
  have hDgraph := actual_contact_disk_graph_clearance D.firstSide D.secondSide
    D.first_on_curve D.second_on_curve D.disk D.disk_embedded D.firstCorner D.secondCorner
    hDmark (fun z hz hzm => D.marks_are_corners z hz hzm) hpositive D.boundary_eq
  exact ⟨D,hDfree.union_right hDgraph,hDcontact⟩

#print axioms actual_original_contact_disk_cleanup_entire_pair_and_graph_private
end CurveComplex.HyperellipticModel
