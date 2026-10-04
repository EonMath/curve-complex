import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalContactDiskCleanupEntirePairGraphPrivate
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

private theorem actual_original_nonloop_given_graph_clear_disk_strict_contact_drop_private
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
    (hDisk : ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
      Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
          (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
      (D.firstCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
        D.secondCorner∈ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)))
    (q : S) (hq : q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
    ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
      (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
      (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
      H.finalMap '' (rT u).val.image=b'.val.image ∧
      Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').Finite ∧
      (∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b',
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) b' q) ∧
      (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').ncard <
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard := by
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
  have actual_selected_original_loop_entire_pair_and_graph_clear_disk
      (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
        (r0 ⟨u.val,hTF u.property⟩).val.map 1)
      (hfinite : (ArcSurgery.crossings M
        (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
      (htransverse : ∀ q ∈ ArcSurgery.crossings M
        (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) q)
      (p : S) (hp : p ∈ ArcSurgery.crossings M
        (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
      ∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        Disjoint D.openInterior
          ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
            (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
          D.secondCorner ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) := by
    exact hDisk
  have actual_essential_closed_piece_strict_drop_assembly
      (a b : EssentialMarkedArc M)
      (hfinite : (ArcSurgery.crossings M a b).Finite)
      (hcross : ∀ p ∈ ArcSurgery.crossings M a b,ArcSurgery.CrossesInDisk M a b p)
      (H : AmbientIsotopy S)
      (hm : ∀ t x,x ∈ M.cover.branch → H.map (t,x)=x)
      (C B R : Set S) (hC : IsCompact C) (hB : IsCompact B)
      (hOld : b.val.image=C ∪ R) (hNew : H.finalMap '' b.val.image=B ∪ R)
      (hBfree : Disjoint B (arcInterior M a))
      (hRfree : Disjoint (R ∩ arcInterior M a) C)
      (hremoved : (ArcSurgery.crossings M a b ∩ C).Nonempty) :
      ∃ b' : EssentialMarkedArc M,
        H.finalMap '' b.val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) b ∧
        ({b'.val.map 0,b'.val.map 1}:Set S)={b.val.map 0,b.val.map 1} ∧
        (ArcSurgery.crossings M a b').Finite ∧
        (∀ p ∈ ArcSurgery.crossings M a b',ArcSurgery.CrossesInDisk M a b' p) ∧
        (ArcSurgery.crossings M a b').ncard < (ArcSurgery.crossings M a b).ncard := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨g,hg⟩ := H.homeomorphism_at (⟨1,by norm_num⟩ : Interval)
    have hgfix : ∀ p, p ∈ M.cover.branch → g p=p :=
      fun p hp => (hg p).trans (hm _ p hp)
    let b' : EssentialMarkedArc M := b.transport g hgfix
    have hcimage : b'.val.image=H.finalMap '' b.val.image := by
      change (b.val.transport g hgfix).image=_
      rw [MarkedArc.transport_image]
      exact congrArg (fun f : S → S => f '' b.val.image) (funext hg)
    have hdecomp : b'.val.image=B ∪ R := hcimage.trans hNew
    have hOldE : b.val.image=C ∪ R := hOld
    have hretain (p : S) (hp : p ∈ ArcSurgery.crossings M a b') :
        p ∈ R ∧ p ∉ C ∪ B := by
      have hpR : p ∈ R := (hdecomp ▸ hp.2.1).resolve_left
        (fun hpB => disjoint_left.mp hBfree hpB hp.1)
      refine ⟨hpR,?_⟩
      rintro (hpC | hpB)
      · exact disjoint_left.mp hRfree ⟨hpR,hp.1⟩ hpC
      · exact disjoint_left.mp hBfree hpB hp.1
    have hsub : ArcSurgery.crossings M a b' ⊆
        ArcSurgery.crossings M a b := by
      intro p hp
      exact ⟨hp.1,⟨hOldE.symm ▸ Or.inr (hretain p hp).1,hp.2.2⟩⟩
    have htrans : ∀ p ∈ ArcSurgery.crossings M a b',
        ArcSurgery.CrossesInDisk M a b' p := by
      intro p hp
      have hsource := actual_marked_crossesInDisk_symm M a b p
        (hcross p (hsub hp))
      have hchanged := actual_closed_replacement_retained_marked_crossing M b
        b' a C B R hC.isClosed hB.isClosed hOld hdecomp p
        hsource (hretain p hp).2
      exact actual_marked_crossesInDisk_symm M b' a p hchanged
    have hclass : Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) b := by
      apply (Quotient.sound ?_).symm
      exact ⟨H,hm,hcimage.symm⟩
    refine ⟨b',hcimage.symm,hclass,?_,hfinite.subset hsub,htrans,?_⟩
    · change ({g (b.val.map 0),g (b.val.map 1)}:Set S)=_
      have h0 : g (b.val.map 0)=b.val.map 0 := hgfix _ b.val.start_marked
      have h1 : g (b.val.map 1)=b.val.map 1 := hgfix _ b.val.end_marked
      rw [h0,h1]
    · apply ncard_lt_ncard _ hfinite
      apply ssubset_iff_subset_ne.mpr
      refine ⟨hsub,?_⟩
      intro heq
      obtain ⟨p,hp,hpC⟩ := hremoved
      have hpnew := heq.symm ▸ hp
      exact (hretain p hpnew).2 (Or.inl hpC)
  have actual_embedded_side_given_strip_produces_graph_clear_full_base_taper_private
      (A : C(Interval,S))
      (E : Interval × Icc (-1:ℝ) 1 → S) (hE : IsEmbedding E)
      (hcenter : ∀ t, E (t,⟨0,by norm_num⟩)=A t) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
        (P : Set S) (hP : IsClosed P) (hbase : A 0 ∈ P)
        (haxis : ∀ t : Interval, 0 < (t:ℝ) →
          A ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩ ∉ P) :
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
        ∃ h : C(Interval,ℝ), h 0=0 ∧
          (∀ t, 0 ≤ h t ∧ h t ≤ ρ) ∧
          (∀ t : Interval, 0 < (t:ℝ) → 0 < h t) ∧
          (∀ t : Interval, (1/2:ℝ) ≤ (t:ℝ) → h t=ρ) ∧
        (∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
          E (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩,v) ∉ P) ∧
        ∃ f : Bool → C(Interval,S),
          (∀ s t, ∃ v : Icc (-1:ℝ) 1,
            (v:ℝ)=(if s then (1:ℝ) else -1)*h t ∧
            f s t=E (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
              (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩,v)) ∧
        ∀ s,
          IsEmbedding (f s) ∧ f s 0=A 0 ∧
          range (f s) ∩ P={A 0} ∧
          range (f s) ∩ range A={A 0} := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI := (actualSphereSmoothAtlas M).charts
    let Z := Interval × Icc (-1:ℝ) 1
    let X : Interval → Z := fun t =>
      (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
        (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩,⟨0,by norm_num⟩)
    have hX : Continuous X := by dsimp [X]; fun_prop
    let F : Set Z := E ⁻¹' P
    have hF : IsClosed F := hP.preimage hE.continuous
    have hzeroE : E (X 0)=A 0 := by
      have hx : X 0=(0,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · apply Subtype.ext; simp [X]
        · rfl
      rw [hx,hcenter]
    have hzeroF : X 0 ∈ F := by
      change E (X 0) ∈ P
      rw [hzeroE]
      exact hbase
    have hFne : F.Nonempty := ⟨X 0,hzeroF⟩
    have haxisF (t : Interval) (ht : 0 < (t:ℝ)) : X t ∉ F := by
      change E (X t) ∉ P
      rw [hcenter]
      exact haxis t ht
    let d : Interval → ℝ := fun t => Metric.infDist (X t) F / 4
    have hd : Continuous d := ((Metric.continuous_infDist_pt F).comp hX).div_const 4
    have hdpos (t : Interval) (ht : 0 < (t:ℝ)) : 0 < d t :=
      div_pos ((hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)) (by norm_num)
    let T : Set Interval := {t | (1/2:ℝ) ≤ (t:ℝ)}
    have hT : IsCompact T := (isClosed_le continuous_const continuous_subtype_val).isCompact
    obtain ⟨δ,hδ,hδd⟩ := hT.exists_forall_le' hd.continuousOn
      (fun t ht => hdpos t (lt_of_lt_of_le (by norm_num) ht))
    let ρ := min δ (1/2)
    have hρ : 0 < ρ := lt_min hδ (by norm_num)
    have hρδ : ρ ≤ δ := min_le_left _ _
    have hρhalf : ρ ≤ 1/2 := min_le_right _ _
    let h : C(Interval,ℝ) := ⟨fun t => min ρ (d t),continuous_const.min hd⟩
    have hn (t : Interval) : 0 ≤ h t :=
      le_min hρ.le (div_nonneg Metric.infDist_nonneg (by norm_num))
    have hb (t : Interval) : h t ≤ ρ := min_le_left _ _
    have hp (t : Interval) (ht : 0 < (t:ℝ)) : 0 < h t := lt_min hρ (hdpos t ht)
    have hzero : h 0=0 := by
      change min ρ (Metric.infDist (X 0) F / 4)=0
      rw [Metric.infDist_zero_of_mem hzeroF,zero_div,min_eq_right hρ.le]
    have htail (t : Interval) (ht : (1/2:ℝ) ≤ (t:ℝ)) : h t=ρ :=
      min_eq_left (hρδ.trans (hδd t ht))
    have hband (t : Interval) (v : Icc (-1:ℝ) 1) (ht : 0 < (t:ℝ))
        (hv : |(v:ℝ)| ≤ h t) : E ((X t).1,v) ∉ P := by
      change ((X t).1,v) ∉ F
      apply Metric.notMem_of_dist_lt_infDist
      have hdist : dist (X t) ((X t).1,v)=|(v:ℝ)| := by
        rw [Prod.dist_eq]
        change max (dist (X t).1 (X t).1) (dist (0:ℝ) (v:ℝ))=|(v:ℝ)|
        simp [Real.dist_eq]
      rw [hdist]
      have hsmall : h t ≤ Metric.infDist (X t) F / 4 := min_le_right _ _
      have hpositive : 0 < Metric.infDist (X t) F :=
        (hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)
      linarith
    let sign : Bool → ℝ := fun s => if s then 1 else -1
    have hsign (s : Bool) : |sign s|=1 := by cases s <;> norm_num [sign]
    let Y : Bool → Interval → Z := fun s t =>
      ((X t).1,⟨sign s*h t,abs_le.mp (by
        rw [abs_mul,hsign,one_mul,abs_of_nonneg (hn t)]
        exact (hb t).trans (hρhalf.trans (by norm_num)))⟩)
    have hY (s : Bool) : Continuous (Y s) := by dsimp [Y,sign,X]; fun_prop
    let f : Bool → C(Interval,S) := fun s => ⟨E ∘ Y s,hE.continuous.comp (hY s)⟩
    have f0 (s : Bool) : f s 0=A 0 := by
      have hy : Y s 0=X 0 := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext; change sign s*h 0=0; rw [hzero,mul_zero]
      change E (Y s 0)=_
      rw [hy,hzeroE]
    have hdist (s : Bool) (t : Interval) : dist (X t) (Y s t)=h t := by
      rw [Prod.dist_eq]
      simp only [Y,Subtype.dist_eq,Real.dist_eq,sub_self,abs_zero,zero_sub,
        abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),max_eq_right (hn t)]
      change max 0 |(0:ℝ)-sign s*h t|=h t
      simp only [zero_sub,abs_neg,abs_mul,hsign,one_mul,abs_of_nonneg (hn t),
        max_eq_right (hn t)]
    have hYP (s : Bool) (t : Interval) (ht : 0 < (t:ℝ)) : Y s t ∉ F := by
      apply Metric.notMem_of_dist_lt_infDist
      rw [hdist]
      have hsmall : h t ≤ Metric.infDist (X t) F / 4 := min_le_right _ _
      have hpositive : 0 < Metric.infDist (X t) F :=
        (hF.notMem_iff_infDist_pos hFne).mp (haxisF t ht)
      linarith
    refine ⟨ρ,hρ,hρhalf,h,hzero,fun t => ⟨hn t,hb t⟩,hp,htail,hband,f,fun s t => ⟨(Y s t).2,rfl,rfl⟩,?_⟩
    intro s
    have hfinj : Function.Injective (f s) := by
      intro t u he
      have hh := congrArg (fun z : Z => (z.1:ℝ)) (hE.injective he)
      change β*(t:ℝ)=β*(u:ℝ) at hh
      exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hβ0) hh)
    refine ⟨((f s).continuous.isClosedEmbedding hfinj).isEmbedding,f0 s,?_,?_⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,htP⟩
        have ht : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          by_contra hne
          exact hYP s t (lt_of_le_of_ne t.property.1 (Ne.symm hne)) htP
        rw [ht,f0 s]
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,f0 s⟩,hbase⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,⟨u,hu⟩⟩
        have he : Y s t=(u,⟨0,by norm_num⟩) :=
          hE.injective (hu.symm.trans (hcenter u).symm)
        have hy : sign s*h t=0 := congrArg (fun q : Z => (q.2:ℝ)) he
        have ht : t=0 := by
          apply Subtype.ext
          change (t:ℝ)=0
          by_contra hne
          have htp := hp t (lt_of_le_of_ne t.property.1 (Ne.symm hne))
          cases s <;> norm_num [sign,ne_of_gt htp] at hy
        rw [ht,f0 s]
        exact mem_singleton _
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,f0 s⟩,mem_range_self _⟩
  have actual_embedded_marked_side_produces_base_vanishing_tracks_private
      (A : C(Interval,S)) (hA : IsEmbedding A) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β < 1)
        (P : Set S) (hP : IsClosed P) (hbase : A 0 ∈ P)
        (haxis : ∀ t : Interval, 0 < (t:ℝ) →
          A ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩ ∉ P) :
        ∃ E : Interval × Icc (-1:ℝ) 1 → S,
          IsEmbedding E ∧ (∀ t, E (t,⟨0,by norm_num⟩)=A t) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1/2 ∧
        ∃ h : C(Interval,ℝ), h 0=0 ∧
          (∀ t, 0 ≤ h t ∧ h t ≤ ρ) ∧
          (∀ t : Interval, 0 < (t:ℝ) → 0 < h t) ∧
          (∀ t : Interval, (1/2:ℝ) ≤ (t:ℝ) → h t=ρ) ∧
        (∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
          E (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v) ∉ P) ∧
        ∃ f : Bool → C(Interval,S),
          (∀ s t, ∃ v : Icc (-1:ℝ) 1,
            (v:ℝ)=(if s then (1:ℝ) else -1)*h t ∧
            f s t=E (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
              (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1.le⟩⟩,v)) ∧
        ∀ s,
          IsEmbedding (f s) ∧ f s 0=A 0 ∧
          range (f s) ∩ P={A 0} ∧
          range (f s) ∩ range A={A 0} := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI := (actualSphereSmoothAtlas M).charts
    obtain ⟨E,hE,hcenter,_⟩ := CurveComplex.source_whole_embedded_arc_strip A hA
      univ isOpen_univ (subset_univ _)
    obtain ⟨ρ,hρ,hρhalf,h,hh0,hbound,hpos,htail,hband,f,hcoords,hf⟩ :=
      actual_embedded_side_given_strip_produces_graph_clear_full_base_taper_private
        A E hE hcenter β hβ0 hβ1.le P hP hbase haxis
    exact ⟨E,hE,hcenter,ρ,hρ,hρhalf,h,hh0,hbound,hpos,htail,hband,f,hcoords,hf⟩
  have actual_essential_marked_prefix_retained_exterior_private
      {κ : Type} (old : κ → EssentialMarkedArc M) (a : EssentialMarkedArc M)
      (hi : ℝ) (hhi0 : 0 < hi) (hhi1 : hi < 1)
      (hportFree : ∀ k, a.val.map (projIcc 0 1 zero_le_one hi) ∉ arcInterior M (old k)) :
      ∃ C R : Set S, IsCompact C ∧ IsCompact R ∧ a.val.image = C ∪ R ∧
        C = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc 0 hi ∧
        C ∩ R = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} ∧
        (∀ k, Disjoint (R ∩ arcInterior M (old k)) C) ∧
        R = (a.val.map ∘ projIcc 0 1 zero_le_one) '' Icc hi 1 ∪ {a.val.map 0} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let g : ℝ → S := a.val.map ∘ projIcc 0 1 zero_le_one
    have hg : Continuous g := a.val.continuous.comp continuous_projIcc
    let C : Set S := g '' Icc 0 hi
    let R : Set S := g '' Icc hi 1 ∪ {a.val.map 0}
    have hc : IsCompact C := isCompact_Icc.image hg
    have hr : IsCompact R := (isCompact_Icc.image hg).union isCompact_singleton
    have hwhole : a.val.image = C ∪ R := by
      apply Subset.antisymm
      · rintro z ⟨t,rfl⟩
        by_cases ht : (t:ℝ) ≤ hi
        · exact Or.inl ⟨(t:ℝ),⟨t.property.1,ht⟩,by simp only [g,Function.comp_apply,projIcc_of_mem zero_le_one t.property]⟩
        · exact Or.inr (Or.inl ⟨(t:ℝ),⟨le_of_not_ge ht,t.property.2⟩,by simp only [g,Function.comp_apply,projIcc_of_mem zero_le_one t.property]⟩)
      · intro z hz
        rcases hz with hz | hz
        · obtain ⟨t,ht,rfl⟩ := hz
          exact mem_range_self _
        · rcases hz with hz | hz
          · obtain ⟨t,ht,rfl⟩ := hz
            exact mem_range_self _
          · exact mem_singleton_iff.mp hz ▸ mem_range_self _
    have hinter : C ∩ R = {a.val.map 0,a.val.map (projIcc 0 1 zero_le_one hi)} := by
      apply Subset.antisymm
      · rintro z ⟨⟨t,ht,he⟩,hzR⟩
        rcases hzR with hzR | hzR
        · obtain ⟨u,hu,hue⟩ := hzR
          have htI : t ∈ Icc (0:ℝ) 1 := ⟨ht.1,ht.2.trans hhi1.le⟩
          have huI : u ∈ Icc (0:ℝ) 1 := ⟨hhi0.le.trans hu.1,hu.2⟩
          rcases a.val.injective_except_loop_closure
              (projIcc 0 1 zero_le_one t) (projIcc 0 1 zero_le_one u)
              (he.trans hue.symm) with htu | htu | htu
          · have htuReal : t = u := by
              have hh := congrArg Subtype.val htu
              simpa only [projIcc_of_mem zero_le_one htI,projIcc_of_mem zero_le_one huI] using hh
            have hthi : t = hi := le_antisymm ht.2 (htuReal ▸ hu.1)
            exact mem_insert_of_mem _ (mem_singleton_iff.mpr (he.symm.trans (by rw [hthi]; rfl)))
          · exact mem_insert_iff.mpr (Or.inl (he.symm.trans (congrArg a.val.map htu.1)))
          · have htt : t=1 := by
              have hh := congrArg Subtype.val htu.1
              simpa only [projIcc_of_mem zero_le_one htI] using hh
            exact False.elim (hhi1.not_ge (htt ▸ ht.2))
        · exact mem_insert_iff.mpr (Or.inl (mem_singleton_iff.mp hzR))
      · intro z hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          exact ⟨⟨0,⟨le_rfl,hhi0.le⟩,by simp [g]⟩,Or.inr (mem_singleton _)⟩
        · have heq := mem_singleton_iff.mp he
          subst z
          exact ⟨⟨hi,⟨hhi0.le,le_rfl⟩,rfl⟩,Or.inl ⟨hi,⟨le_rfl,hhi1.le⟩,rfl⟩⟩
    refine ⟨C,R,hc,hr,hwhole,rfl,hinter,?_,rfl⟩
    intro k
    apply Set.disjoint_left.mpr
    intro z hzR hzC
    have hz := hinter ▸ (show z ∈ C ∩ R from ⟨hzC,hzR.1⟩)
    rcases mem_insert_iff.mp hz with he | he
    · exact hzR.2.2 (he.symm ▸ a.val.start_marked)
    · exact hportFree k ((mem_singleton_iff.mp he) ▸ hzR.2)
  have actual_original_pair_entire_graph_contact_is_marked :
      ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image) ∩
        actualObjectTrace M r J ⊆ (M.cover.branch : Set S) := by
    rintro z ⟨hzpair,hzgraph⟩
    by_contra hzm
    rw [←hgraph] at hzgraph
    obtain ⟨v,hv⟩ := mem_iUnion.mp hzgraph
    obtain ⟨hvJ,hzv⟩ := mem_iUnion.mp hv
    have hneF : v ≠ ⟨u.val,hTF u.property⟩ := by
      intro he
      exact hu (congrArg Subtype.val he ▸ hvJ)
    rcases hzpair with hza | hzb
    · exact disjoint_left.mp (hd0 v _ hneF) ⟨hzv,hzm⟩ ⟨hza,hzm⟩
    · let vT : {w // w ∈ T.val} := ⟨v.val,hJT hvJ⟩
      have hneT : vT ≠ u := by
        intro he
        exact hu (congrArg Subtype.val he ▸ hvJ)
      have heF : (⟨vT.val,hTF vT.property⟩ : {w // w ∈ F})=v := Subtype.ext rfl
      have hrv : r0 v=rT vT := by simpa only [heF] using haligned0 vT hvJ
      rw [hrv] at hzv
      exact disjoint_left.mp (hdT vT hvJ) ⟨hzv,hzm⟩ ⟨hzb,hzm⟩
  have actual_original_pair_closed_obstacle_contact_is_marked :
      ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image) ∩
        ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ⊆
        (M.cover.branch : Set S) := by
    rintro z ⟨hzpair,hzm | hzG⟩
    · exact hzm
    · exact actual_original_pair_entire_graph_contact_is_marked ⟨hzpair,hzG⟩
  have actual_compact_mark_free_original_carrier_has_padded_parameters
      (c : EssentialMarkedArc M) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hsub : range f ⊆ arcInterior M c) :
      ∃ α β : ℝ, ∃ τ : C(Interval,ℝ),
        0 < α ∧ α < β ∧ β < 1 ∧
        (∀ t,α < τ t ∧ τ t < β) ∧
        (∀ t,c.val.map (projIcc 0 1 zero_le_one (τ t))=f t) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨q,hq⟩ := hActualInteriorParameterHomeomorph M c
    let point : C(Interval,arcInterior M c) :=
      ⟨fun t => ⟨f t,hsub (Set.mem_range_self t)⟩,f.continuous.subtype_mk _⟩
    let τ : C(Interval,ℝ) := ⟨fun t => (q.symm (point t)).val.val,
      continuous_subtype_val.comp (continuous_subtype_val.comp (q.symm.continuous.comp point.continuous))⟩
    have hτf (t : Interval) : c.val.map (q.symm (point t)).val=f t := by
      rw [← hq]
      exact congrArg Subtype.val (q.apply_symm_apply _)
    have hτ01 (t : Interval) : 0 < τ t ∧ τ t < 1 := by
      have hm : c.val.map (q.symm (point t)).val ∉ M.cover.branch := (q.symm (point t)).property.2
      constructor
      · have hn : (q.symm (point t)).val ≠ 0 := fun he => hm (he.symm ▸ c.val.start_marked)
        exact lt_of_le_of_ne (q.symm (point t)).val.property.1 (fun he => hn (Subtype.ext he.symm))
      · have hn : (q.symm (point t)).val ≠ 1 := fun he => hm (he.symm ▸ c.val.end_marked)
        exact lt_of_le_of_ne (q.symm (point t)).val.property.2 (fun he => hn (Subtype.ext he))
    let C : Set ℝ := range τ
    have hC : IsCompact C := isCompact_range τ.continuous
    have hCne : C.Nonempty := Set.range_nonempty τ
    let l := sInf C
    let u := sSup C
    have hl : l ∈ C := hC.isClosed.csInf_mem hCne hC.bddBelow
    have hu : u ∈ C := hC.isClosed.csSup_mem hCne hC.bddAbove
    have hl0 : 0 < l := by obtain ⟨t,ht⟩ := hl; exact ht ▸ (hτ01 t).1
    have hu1 : u < 1 := by obtain ⟨t,ht⟩ := hu; exact ht ▸ (hτ01 t).2
    have hlu : l ≤ u := csInf_le hC.bddBelow hu
    let α := l/2
    let β := (u+1)/2
    have hα : 0 < α := half_pos hl0
    have hβ : β < 1 := by dsimp [β]; linarith
    have hαβ : α < β := by dsimp [α,β]; linarith
    refine ⟨α,β,τ,hα,hαβ,hβ,?_,?_⟩
    · intro t
      have hτC : τ t ∈ C := mem_range_self t
      have hlo : l ≤ τ t := csInf_le hC.bddBelow hτC
      have hhi : τ t ≤ u := le_csSup hC.bddAbove hτC
      dsimp [α,β]
      constructor <;> linarith
    · intro t
      rw [Set.projIcc_of_mem zero_le_one ⟨(hτ01 t).1.le,(hτ01 t).2.le⟩]
      exact hτf t
  have actual_compact_axis_uniform_band_inside_open
      (R : Interval × Icc (-1:ℝ) 1 → S) (hR : Continuous R)
      (q : Interval → Interval) (hq : Continuous q)
      (U : Set S) (hU : IsOpen U)
      (haxis : ∀ t,R (q t,⟨0,by norm_num⟩) ∈ U) :
      ∃ ρ : ℝ,0 < ρ ∧ ρ ≤ 1/2 ∧
        ∀ (t : Interval) (v : Icc (-1:ℝ) 1),|(v:ℝ)| ≤ ρ → R (q t,v) ∈ U := by
    let Z := Interval × Icc (-1:ℝ) 1
    let X : Interval → Z := fun t => (q t,⟨0,by norm_num⟩)
    have hX : Continuous X := hq.prodMk continuous_const
    have hK : IsCompact (range X) := isCompact_range hX
    obtain ⟨δ,hδ,hband⟩ := hK.exists_cthickening_subset_open (hU.preimage hR)
      (by rintro z ⟨t,rfl⟩; exact haxis t)
    let ρ : ℝ := min δ (1/2)
    refine ⟨ρ,lt_min hδ (by norm_num),min_le_right _ _,?_⟩
    intro t v hv
    apply hband
    apply Metric.mem_cthickening_of_dist_le (q t,v) (X t) δ (range X) (mem_range_self t)
    have hd : dist (q t,v) (X t)=|(v:ℝ)| := by
      simp [X,Prod.dist_eq,Subtype.dist_eq,Real.dist_eq]
    rw [hd]
    exact hv.trans (min_le_left _ _)
  have actual_compact_original_carrier_closed_strip_inside_open
      (c : EssentialMarkedArc M) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hsub : range f ⊆ arcInterior M c)
      (U : Set S) (hU : IsOpen U) (hfU : range f ⊆ U) :
      ∃ R : Interval × Icc (-1:ℝ) 1 → S,
        IsEmbedding R ∧ range R ⊆ U ∧
        (∀ t,R (t,⟨0,by norm_num⟩)=f t) ∧
        (∀ z,R z ∉ M.cover.branch) ∧
        (∀ z,R z ∈ c.val.image ↔ z.2.val=0) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨α,β,τ,hα,hαβ,hβ,hτ,hτf⟩ :=
      actual_compact_mark_free_original_carrier_has_padded_parameters c f hf hsub
    obtain ⟨B,hB,hcenter,hmarks,haxis⟩ :=
      ArcSurgery.actual_anchor_interior_core_exact_strip M c α β hα hβ hαβ
    let q : Interval → Interval := fun t =>
      ⟨(τ t-α)/(β-α),by
        constructor
        · exact (div_pos (sub_pos.mpr (hτ t).1) (sub_pos.mpr hαβ)).le
        · exact ((div_lt_one (sub_pos.mpr hαβ)).mpr (by linarith [(hτ t).2])).le⟩
    have hq : Continuous q := by fun_prop
    have hc (t : Interval) : B (q t,⟨0,by norm_num⟩)=f t := by
      rw [hcenter]
      have hp : ArcSurgery.actualCoreParameter α β hα.le hβ.le hαβ.le (q t)=
          projIcc 0 1 zero_le_one (τ t) := by
        rw [Set.projIcc_of_mem zero_le_one ⟨hα.le.trans (hτ t).1.le,(hτ t).2.le.trans hβ.le⟩]
        apply Subtype.ext
        dsimp [ArcSurgery.actualCoreParameter,q]
        field_simp [ne_of_gt (sub_pos.mpr hαβ)]
        <;> ring
      rw [hp]
      exact hτf t
    have hqi : Function.Injective q := by
      intro t u he
      apply hf.injective
      rw [←hc t,←hc u,he]
    obtain ⟨ρ,hρ,hρhalf,hband⟩ := actual_compact_axis_uniform_band_inside_open
      B hB.continuous q hq U hU (fun t => hc t ▸ hfU (mem_range_self t))
    let v : Icc (-1:ℝ) 1 → Icc (-1:ℝ) 1 := fun x =>
      ⟨ρ*x.val,by constructor <;> nlinarith [x.property.1,x.property.2]⟩
    let R : Interval × Icc (-1:ℝ) 1 → S := fun z => B (q z.1,v z.2)
    have hRi : Function.Injective R := by
      intro z w he
      have he' := hB.injective he
      apply Prod.ext
      · exact hqi (congrArg Prod.fst he')
      · apply Subtype.ext
        have hv := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => z.2.val) he'
        dsimp [v] at hv
        nlinarith
    have hRc : Continuous R := hB.continuous.comp (hq.comp continuous_fst |>.prodMk (by fun_prop))
    refine ⟨R,hRc.isClosedEmbedding hRi |>.isEmbedding,?_,?_,?_,?_⟩
    · rintro z ⟨x,rfl⟩
      apply hband
      change |ρ*x.2.val| ≤ ρ
      rw [abs_mul,abs_of_pos hρ]
      have hx : |x.2.val| ≤ 1 := abs_le.mpr x.2.property
      nlinarith
    · intro t
      simpa [R,v] using hc t
    · intro z
      exact hmarks _
    · intro z
      rw [haxis]
      change ρ*z.2.val=0 ↔ z.2.val=0
      exact mul_eq_zero.trans (by simp [ne_of_gt hρ])
  have actual_essential_mark_free_support_disk_retained_remainder
      (a b : EssentialMarkedArc M) (u v : Interval) (c g : C(Interval,S))
      (hu : b.val.map u=g 0) (hv : b.val.map v=g 1)
      (hc : range c=b.val.map '' uIcc u v)
      (hgA : Disjoint (range g) a.val.image)
      (hgB : range g ∩ b.val.image={g 0,g 1})
      (e : C(Metric.closedBall (0 : Plane) 1,S)) (he : IsEmbedding e)
      (heb : e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range c ∪ range g)
      (heMarks : Disjoint (range e) (M.cover.branch:Set S)) :
      ∃ R : Set S,IsCompact R ∧ b.val.image=range c ∪ R ∧
        (∀ z ∈ range c ∩ R,z=g 0 ∨ z=g 1) ∧
        Disjoint (R ∩ arcInterior M a) (range c) ∧
        Disjoint (e '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) R := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    letI := (actualSphereSmoothAtlas M).charts
    letI := (actualSphereSmoothAtlas M).manifold
    let lo : Interval := min u v
    let hi : Interval := max u v
    have hC : range c=b.val.map '' Icc lo hi := hc
    have hlohi : lo ≤ hi := min_le_max
    have hCbd : range c ⊆ e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := heb.symm ▸ subset_union_left
    have hloC : b.val.map lo ∈ range c := hC.symm ▸ ⟨lo,⟨le_rfl,hlohi⟩,rfl⟩
    have hhiC : b.val.map hi ∈ range c := hC.symm ▸ ⟨hi,⟨hlohi,le_rfl⟩,rfl⟩
    have hlo : (0:Interval) < lo := by
      apply lt_of_le_of_ne (show (0:Interval) ≤ lo from bot_le)
      intro hz
      have hc0 : b.val.map (0:Interval) ∈ range c := hz.symm ▸ hloC
      have hm0 : b.val.map (0:Interval) ∈ M.cover.branch := b.val.start_marked
      exact disjoint_left.mp heMarks (image_subset_range _ _ (hCbd hc0)) hm0
    have hhi : hi < (1:Interval) := by
      apply lt_of_le_of_ne (show hi ≤ (1:Interval) from le_top)
      intro hz
      have hc1 : b.val.map (1:Interval) ∈ range c := hz ▸ hhiC
      have hm1 : b.val.map (1:Interval) ∈ M.cover.branch := b.val.end_marked
      exact disjoint_left.mp heMarks (image_subset_range _ _ (hCbd hc1)) hm1
    have hportlo : b.val.map lo=g 0 ∨ b.val.map lo=g 1 := by
      by_cases huv : u ≤ v
      · left; simpa only [lo,min_eq_left huv] using hu
      · right; simpa only [lo,min_eq_right (le_of_not_ge huv)] using hv
    have hporthi : b.val.map hi=g 0 ∨ b.val.map hi=g 1 := by
      by_cases huv : u ≤ v
      · right; simpa only [hi,max_eq_right huv] using hv
      · left; simpa only [hi,max_eq_left (le_of_not_ge huv)] using hu
    let R : Set S := b.val.map '' (Iic lo ∪ Ici hi)
    have hR : IsCompact R := (isClosed_Iic.union isClosed_Ici).isCompact.image b.val.continuous
    have hRb : R ⊆ b.val.image := image_subset_range _ _
    have hOld : b.val.image=range c ∪ R := by
      rw [hC]
      apply Subset.antisymm
      · rintro z ⟨t,rfl⟩
        by_cases htl : t ≤ lo
        · exact Or.inr ⟨t,Or.inl htl,rfl⟩
        by_cases hth : hi ≤ t
        · exact Or.inr ⟨t,Or.inr hth,rfl⟩
        exact Or.inl ⟨t,⟨(le_of_not_ge htl),(le_of_not_ge hth)⟩,rfl⟩
      · intro z hz
        rcases hz with hz | hz
        · exact image_subset_range _ _ hz
        · exact hRb hz
    have hsourceinj (s t : Interval) (hs : s ∈ Icc lo hi)
        (heq : b.val.map s=b.val.map t) : s=t := by
      have hsMark : b.val.map s ∉ M.cover.branch := by
        intro hm
        exact disjoint_left.mp heMarks (image_subset_range _ _ (hCbd (hC.symm ▸ ⟨s,hs,rfl⟩))) hm
      rcases b.val.injective_except_loop_closure s t heq with h | h | h
      · exact h
      · exact False.elim (hsMark (h.1.symm ▸ b.val.start_marked))
      · exact False.elim (hsMark (h.1.symm ▸ b.val.end_marked))
    have hCR : ∀ z ∈ range c ∩ R, z=g 0 ∨ z=g 1 := by
      rintro z ⟨hzc,⟨t,ht,htz⟩⟩
      obtain ⟨s,hs,hsz⟩ := hC ▸ hzc
      have hst : s=t := hsourceinj s t hs (hsz.trans htz.symm)
      subst s
      rcases ht with ht | ht
      · have heq : t=lo := le_antisymm ht hs.1
        exact htz.symm ▸ (heq ▸ hportlo)
      · have heq : t=hi := le_antisymm hs.2 ht
        exact htz.symm ▸ (heq ▸ hporthi)
    have hRfree : Disjoint (R ∩ arcInterior M a) (range c) := by
      apply disjoint_left.mpr
      intro z hzR hzC
      rcases hCR z ⟨hzC,hzR.1⟩ with heq | heq
      · exact disjoint_left.mp hgA (heq ▸ mem_range_self 0) hzR.2.1
      · exact disjoint_left.mp hgA (heq ▸ mem_range_self 1) hzR.2.1
    have hfrontB : frontier (range e) ∩ b.val.image ⊆ range c := by
      intro z hz
      have hbdy := CurveComplex.embedded_disk_frontier_subset_boundary e he hz.1
      rcases heb ▸ hbdy with hzc | hzg
      · exact hzc
      · have hp : z ∈ ({g 0,g 1}:Set S) := hgB ▸ (show z ∈ range g ∩ b.val.image from ⟨hzg,hz.2⟩)
        rcases mem_insert_iff.mp hp with hp | hp
        · subst z
          exact hu ▸ (hC.symm ▸ ⟨u,⟨min_le_left _ _,le_max_left _ _⟩,rfl⟩)
        · have hp := mem_singleton_iff.mp hp
          subst z
          exact hv ▸ (hC.symm ▸ ⟨v,⟨min_le_right _ _,le_max_right _ _⟩,rfl⟩)
    have hLavoid : Disjoint (b.val.map '' Iio lo) (frontier (range e)) := by
      apply disjoint_left.mpr
      rintro z ⟨t,ht,rfl⟩ hzF
      obtain ⟨s,hs,heq⟩ := hC ▸ hfrontB ⟨hzF,mem_range_self t⟩
      have hst := hsourceinj s t hs heq
      exact (not_le_of_gt ht) (hst ▸ hs.1)
    have hUavoid : Disjoint (b.val.map '' Ioi hi) (frontier (range e)) := by
      apply disjoint_left.mpr
      rintro z ⟨t,ht,rfl⟩ hzF
      obtain ⟨s,hs,heq⟩ := hC ▸ hfrontB ⟨hzF,mem_range_self t⟩
      have hst := hsourceinj s t hs heq
      exact (not_le_of_gt ht) (hst ▸ hs.2)
    have hLout : b.val.map '' Iio lo ⊆ (range e)ᶜ := by
      rcases CurveComplex.connected_cap_side (range e) (b.val.map '' Iio lo)
        (isPreconnected_Iio.image _ b.val.continuous.continuousOn) hLavoid with hIn | hOut
      · have hp := interior_subset (hIn ⟨0,hlo,rfl⟩)
        exact False.elim (disjoint_left.mp heMarks hp b.val.start_marked)
      · exact hOut.trans interior_subset
    have hUout : b.val.map '' Ioi hi ⊆ (range e)ᶜ := by
      rcases CurveComplex.connected_cap_side (range e) (b.val.map '' Ioi hi)
        (isPreconnected_Ioi.image _ b.val.continuous.continuousOn) hUavoid with hIn | hOut
      · have hp := interior_subset (hIn ⟨1,hhi,rfl⟩)
        exact False.elim (disjoint_left.mp heMarks hp b.val.end_marked)
      · exact hOut.trans interior_subset
    refine ⟨R,hR,hOld,hCR,hRfree,?_⟩
    apply disjoint_left.mpr
    rintro z hzIn ⟨t,ht,rfl⟩
    rcases ht with ht | ht
    · rcases lt_or_eq_of_le (show t ≤ lo from ht) with ht | ht
      · exact hLout ⟨t,ht,rfl⟩ (image_subset_range _ _ hzIn)
      · exact disjoint_left.mp (CurveComplex.embedded_disk_interior_disjoint_boundary e he) hzIn (ht.symm ▸ hCbd hloC)
    · rcases lt_or_eq_of_le (show hi ≤ t from ht) with ht | ht
      · exact hUout ⟨t,ht,rfl⟩ (image_subset_range _ _ hzIn)
      · exact disjoint_left.mp (CurveComplex.embedded_disk_interior_disjoint_boundary e he) hzIn (ht ▸ hCbd hhiC)
  have actual_original_inner_disk_side_strip_avoids_entire_graph
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch) :
      ∃ R : Interval × Icc (-1:ℝ) 1 → S,
        IsEmbedding R ∧
        (∀ t,R (t,⟨0,by norm_num⟩)=D.firstSide t) ∧
        Disjoint (range R) ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (∀ z,R z ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ↔ z.2.val=0) := by
    letI : T2Space S := M.sphere.symm.t2Space
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    have hQc : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    have hsideMark : Disjoint (range D.firstSide) (M.cover.branch : Set S) := by
      apply disjoint_left.mpr
      intro z hz hzm
      have hzd : z ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show z ∈ range D.firstSide ∪ range D.secondSide from Or.inl hz))
      rcases mem_insert_iff.mp (D.marks_are_corners z hzd hzm) with hz0 | hz1
      · exact h0 (hz0 ▸ hzm)
      · exact h1 (mem_singleton_iff.mp hz1 ▸ hzm)
    have hside : range D.firstSide ⊆ arcInterior M (r0 ⟨u.val,hTF u.property⟩) :=
      fun z hz => ⟨D.first_on_curve hz,disjoint_left.mp hsideMark hz⟩
    have hsideU : range D.firstSide ⊆ Qᶜ := by
      intro z hz hzQ
      have hpair : z ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image :=
        Or.inl (D.first_on_curve hz)
      exact disjoint_left.mp hsideMark hz
        (actual_original_pair_closed_obstacle_contact_is_marked ⟨hpair,hzQ⟩)
    obtain ⟨R,hR,hRU,hcenter,hmarks,haxis⟩ :=
      actual_compact_original_carrier_closed_strip_inside_open
        (r0 ⟨u.val,hTF u.property⟩) D.firstSide D.first_embedded hside Qᶜ hQc.isOpen_compl hsideU
    exact ⟨R,hR,hcenter,disjoint_left.mpr (fun z hz hzQ => hRU hz hzQ),haxis⟩
  have actual_original_inner_empty_disk_enlarged_away_from_entire_graph
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hDG : Disjoint D.openInterior (actualObjectTrace M r J)) :
      ∃ d : C(Metric.closedBall (0 : Plane) 1,S),IsEmbedding d ∧
        range D.disk ⊆ interior (range d) ∧
        Disjoint (range d) ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) := by
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
    letI : CurveComplex.ClosedSurface S := {}
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    have hQc : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    have hDmarks : Disjoint (range D.disk) (M.cover.branch : Set S) := by
      apply disjoint_left.mpr
      intro z hz hzm
      rcases mem_insert_iff.mp (D.marks_are_corners z hz hzm) with he | he
      · exact h0 (he ▸ hzm)
      · exact h1 (mem_singleton_iff.mp he ▸ hzm)
    have hDQ : range D.disk ⊆ Qᶜ := by
      rintro z ⟨x,hxz⟩ hQ
      rcases hQ with hmark | hgraph
      · exact disjoint_left.mp hDmarks ⟨x,hxz⟩ hmark
      have hnorm : ‖x.val‖ ≤ 1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
      rcases hnorm.lt_or_eq with hin | hbd
      · exact disjoint_left.mp hDG
          ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hin,hxz⟩ hgraph
      · have hboundary : z ∈ range D.firstSide ∪ range D.secondSide := by
          rw [←D.boundary_eq]
          exact ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hbd,hxz⟩
        have hpair : z ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image :=
          hboundary.imp (fun h => D.first_on_curve h) (fun h => D.second_on_curve h)
        have hm := actual_original_pair_entire_graph_contact_is_marked ⟨hpair,hgraph⟩
        exact disjoint_left.mp hDmarks ⟨x,hxz⟩ hm
    obtain ⟨H,d,hd,hstrict,hdQ,_,_,_⟩ :=
      CurveComplex.LocalSurgery.exists_supported_strict_disk_enlargement
        D.disk D.disk_embedded Qᶜ hQc.isOpen_compl hDQ
    exact ⟨d,hd,hstrict,disjoint_left.mpr (fun z hz hzQ => hdQ hz hzQ)⟩
  have actual_original_inner_disk_two_endpoint_crossing_framed_graph_clear_strip
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (F : Bool → OpenPartialHomeomorph S Plane)
        (R : Interval × Icc (-1:ℝ) 1 → S),
        (∀ k,Disjoint (F k).source ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
          D.firstSide (if k then 1 else 0) ∈ (F k).source ∧
          F k (D.firstSide (if k then 1 else 0))=0 ∧
          (∀ x ∈ (F k).source,x ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ↔ F k x 1=0) ∧
          (∀ x ∈ (F k).source,x ∈ (rT u).val.image ↔ F k x 0=0)) ∧
        IsEmbedding R ∧
        Disjoint (range R) ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (∀ t,R (t,⟨0,by norm_num⟩)=D.firstSide t) ∧
        ∃ σ δ η : Bool → ℝ,
          (∀ k,σ k = -1 ∨ σ k=1) ∧ (∀ k,0 < δ k ∧ 0 < η k) ∧
          ∀ k (t : Interval) (v : Icc (-1:ℝ) 1),
            |(t:ℝ)-((if k then 1 else 0):ℝ)| < η k →
            R (t,v) ∈ (F k).source ∧
            F k (R (t,v))=Plane.mk (F k (D.firstSide t) 0) (σ k*δ k*(v:ℝ)) := by
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
    letI : CurveComplex.ClosedSurface S := {}
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    have hQc : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    let corner : Bool → S := fun k => if k then D.secondCorner else D.firstCorner
    have hcornerA (k : Bool) : corner k ∈ a.val.image := by
      cases k
      · exact D.first_on_curve ⟨0,D.first_zero⟩
      · exact D.first_on_curve ⟨1,D.first_one⟩
    have hcornerB (k : Bool) : corner k ∈ b.val.image := by
      cases k
      · exact D.second_on_curve ⟨0,D.second_zero⟩
      · exact D.second_on_curve ⟨1,D.second_one⟩
    have hfree (k : Bool) : corner k ∉ M.cover.branch := by cases k <;> assumption
    have hcornerQ (k : Bool) : corner k ∈ Qᶜ := by
      intro hz
      exact hfree k (actual_original_pair_closed_obstacle_contact_is_marked
        ⟨Or.inl (hcornerA k),hz⟩)
    have hcharts (k : Bool) : ∃ G : OpenPartialHomeomorph S Plane,
        G.source ⊆ Qᶜ ∧ Disjoint G.source (M.cover.branch:Set S) ∧
        corner k ∈ G.source ∧ G (corner k)=0 ∧
        (∀ x ∈ G.source, x ∈ a.val.image ↔ G x 1=0) ∧
        (∀ x ∈ G.source, x ∈ b.val.image ↔ G x 0=0) := by
      obtain ⟨U,hU,hpU,hm,e,hep,ha,hb⟩ := hcross (corner k)
        ⟨⟨hcornerA k,hfree k⟩,hcornerB k,hfree k⟩
      let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
      have hV : IsOpen V := (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
      letI : Nonempty U := ⟨⟨corner k,hpU⟩⟩
      let coeU := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
      let f : U → ℝ × ℝ := fun u => (e u:ℝ × ℝ)
      have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
      let coeE := hf.toOpenPartialHomeomorph f
      let E0 := coeU.symm.trans coeE
      have hEs : E0.source=U := by simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
      have hE (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩:ℝ × ℝ) := by
        have hu : coeU.symm x=⟨x,hx⟩ := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
        change f (coeU.symm x)=_
        rw [hu]
      let L : (ℝ × ℝ) ≃ₜ Plane := {
        toEquiv := {
          toFun := fun z => Plane.mk z.1 z.2
          invFun := fun z => (z 0,z 1)
          left_inv := by intro z; apply Prod.ext <;> rfl
          right_inv := by intro z; ext j; fin_cases j <;> rfl }
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let G := (E0.restr (Qᶜ)).trans L.toOpenPartialHomeomorph
      have hGs : G.source=U ∩ Qᶜ := by simp [G,hEs]
      have hG (x : S) (hx : x ∈ U) : G x=Plane.mk (e ⟨x,hx⟩).val.1 (e ⟨x,hx⟩).val.2 := by
        change L (E0 x)=_
        rw [hE x hx]; rfl
      refine ⟨G,fun x hx => (hGs.le hx).2,hm.mono_left (fun x hx => (hGs.le hx).1),
        hGs.symm ▸ ⟨hpU,hcornerQ k⟩,?_,?_,?_⟩
      · rw [hG _ hpU,hep]; ext j; fin_cases j <;> rfl
      · intro x hx
        rw [hG x (hGs.le hx).1]
        exact ha ⟨x,(hGs.le hx).1⟩
      · intro x hx
        rw [hG x (hGs.le hx).1]
        exact hb ⟨x,(hGs.le hx).1⟩
    choose F hFN hFm hFp hF0 hFa hFb using hcharts
    let θ : Bool → Interval := fun k => if k then 1 else 0
    have hθ : Function.Injective θ := by
      intro k l he
      cases k <;> cases l <;> simp [θ] at he ⊢
    have hcorner (k : Bool) : D.firstSide (θ k)=corner k := by
      cases k
      · exact D.first_zero
      · exact D.first_one
    have hsideQ : range D.firstSide ⊆ Qᶜ := by
      intro z hz hzQ
      have hzm := actual_original_pair_closed_obstacle_contact_is_marked
        ⟨Or.inl (D.first_on_curve hz),hzQ⟩
      have hzD : z ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show z ∈ range D.firstSide ∪ range D.secondSide from Or.inl hz))
      rcases mem_insert_iff.mp (D.marks_are_corners z hzD hzm) with he | he
      · exact h0 (he ▸ hzm)
      · exact h1 (mem_singleton_iff.mp he ▸ hzm)
    obtain ⟨R,hR,hRQ,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ :=
      CurveComplex.source_finite_axis_framed_arc_strip S D.firstSide D.first_embedded
        Bool θ hθ F (fun k => hcorner k ▸ hFp k)
        (fun k => by rw [hcorner]; exact hF0 k)
        (fun k t ht => (hFa k _ ht).mp (D.first_on_curve (mem_range_self t)))
        Qᶜ hQc.isOpen_compl hsideQ
    refine ⟨F,R,?_,hR,disjoint_left.mpr (fun z hz hzQ => hRQ hz hzQ),
      hcenter,σ,δ,η,hsign,hpos,?_⟩
    · intro k
      refine ⟨disjoint_left.mpr (fun z hz hzQ => hFN k hz hzQ),?_,?_,hFa k,hFb k⟩
      · exact hcorner k ▸ hFp k
      · rw [hcorner]; exact hF0 k
    · intro k t v ht
      apply hcoords k t v
      cases k <;> simpa [θ] using ht
  have actual_original_marked_half_disk_terminal_crossing_framed_full_side_strip_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h1 : D.secondCorner ∉ M.cover.branch)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (F : Unit → OpenPartialHomeomorph S Plane)
        (R : Interval × Icc (-1:ℝ) 1 → S),
        (∀ k,Disjoint (F k).source ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
          D.firstSide (1:Interval) ∈ (F k).source ∧
          F k (D.firstSide (1:Interval))=0 ∧
          (∀ x ∈ (F k).source,x ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ↔ F k x 1=0) ∧
          (∀ x ∈ (F k).source,x ∈ (rT u).val.image ↔ F k x 0=0)) ∧
        IsEmbedding R ∧
        (∀ t,R (t,⟨0,by norm_num⟩)=D.firstSide t) ∧
        ∃ σ δ η : Unit → ℝ,
          (∀ k,σ k = -1 ∨ σ k=1) ∧ (∀ k,0 < δ k ∧ 0 < η k) ∧
          ∀ k (t : Interval) (v : Icc (-1:ℝ) 1),
            |(t:ℝ)-((1:Interval):ℝ)| < η k →
            R (t,v) ∈ (F k).source ∧
            F k (R (t,v))=Plane.mk (F k (D.firstSide t) 0) (σ k*δ k*(v:ℝ)) := by
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
    letI : CurveComplex.ClosedSurface S := {}
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    have hQc : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    let corner : Unit → S := fun _ => D.secondCorner
    have hcornerA (k : Unit) : corner k ∈ a.val.image := D.first_on_curve ⟨1,D.first_one⟩
    have hcornerB (k : Unit) : corner k ∈ b.val.image := D.second_on_curve ⟨1,D.second_one⟩
    have hfree (k : Unit) : corner k ∉ M.cover.branch := h1
    have hcornerQ (k : Unit) : corner k ∈ Qᶜ := by
      intro hz
      exact hfree k (actual_original_pair_closed_obstacle_contact_is_marked
        ⟨Or.inl (hcornerA k),hz⟩)
    have hcharts (k : Unit) : ∃ G : OpenPartialHomeomorph S Plane,
        G.source ⊆ Qᶜ ∧ Disjoint G.source (M.cover.branch:Set S) ∧
        corner k ∈ G.source ∧ G (corner k)=0 ∧
        (∀ x ∈ G.source, x ∈ a.val.image ↔ G x 1=0) ∧
        (∀ x ∈ G.source, x ∈ b.val.image ↔ G x 0=0) := by
      obtain ⟨U,hU,hpU,hm,e,hep,ha,hb⟩ := hcross (corner k)
        ⟨⟨hcornerA k,hfree k⟩,hcornerB k,hfree k⟩
      let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
      have hV : IsOpen V := (isOpen_lt (continuous_fst.abs) continuous_const).inter
        (isOpen_lt (continuous_snd.abs) continuous_const)
      letI : Nonempty U := ⟨⟨corner k,hpU⟩⟩
      let coeU := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph Subtype.val
      let f : U → ℝ × ℝ := fun u => (e u:ℝ × ℝ)
      have hf : IsOpenEmbedding f := hV.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding
      let coeE := hf.toOpenPartialHomeomorph f
      let E0 := coeU.symm.trans coeE
      have hEs : E0.source=U := by simp [E0,coeU,coeE,IsOpenEmbedding.toOpenPartialHomeomorph_target]
      have hE (x : S) (hx : x ∈ U) : E0 x=(e ⟨x,hx⟩:ℝ × ℝ) := by
        have hu : coeU.symm x=⟨x,hx⟩ := hU.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv (x := ⟨x,hx⟩)
        change f (coeU.symm x)=_
        rw [hu]
      let L : (ℝ × ℝ) ≃ₜ Plane := {
        toEquiv := {
          toFun := fun z => Plane.mk z.1 z.2
          invFun := fun z => (z 0,z 1)
          left_inv := by intro z; apply Prod.ext <;> rfl
          right_inv := by intro z; ext j; fin_cases j <;> rfl }
        continuous_toFun := by fun_prop
        continuous_invFun := by fun_prop }
      let G := (E0.restr (Qᶜ)).trans L.toOpenPartialHomeomorph
      have hGs : G.source=U ∩ Qᶜ := by simp [G,hEs]
      have hG (x : S) (hx : x ∈ U) : G x=Plane.mk (e ⟨x,hx⟩).val.1 (e ⟨x,hx⟩).val.2 := by
        change L (E0 x)=_
        rw [hE x hx]; rfl
      refine ⟨G,fun x hx => (hGs.le hx).2,hm.mono_left (fun x hx => (hGs.le hx).1),
        hGs.symm ▸ ⟨hpU,hcornerQ k⟩,?_,?_,?_⟩
      · rw [hG _ hpU,hep]; ext j; fin_cases j <;> rfl
      · intro x hx
        rw [hG x (hGs.le hx).1]
        exact ha ⟨x,(hGs.le hx).1⟩
      · intro x hx
        rw [hG x (hGs.le hx).1]
        exact hb ⟨x,(hGs.le hx).1⟩
    choose F hFN hFm hFp hF0 hFa hFb using hcharts
    let θ : Unit → Interval := fun _ => 1
    have hθ : Function.Injective θ := fun k l _ => Subsingleton.elim k l
    have hcorner (k : Unit) : D.firstSide (θ k)=corner k := D.first_one
    obtain ⟨R,hR,hRQ,hcenter,σ,δ,η,hsign,hpos,hcoords⟩ :=
      CurveComplex.source_finite_axis_framed_arc_strip S D.firstSide D.first_embedded
        Unit θ hθ F (fun k => hcorner k ▸ hFp k)
        (fun k => by rw [hcorner k]; exact hF0 k)
        (fun k t ht => (hFa k _ ht).mp (D.first_on_curve (mem_range_self t)))
        univ isOpen_univ (subset_univ _)
    refine ⟨F,R,?_,hR,
      hcenter,σ,δ,η,hsign,hpos,?_⟩
    · intro k
      refine ⟨disjoint_left.mpr (fun z hz hzQ => hFN k hz hzQ),?_,?_,hFa k,hFb k⟩
      · exact hcorner k ▸ hFp k
      · rw [hcorner k]; exact hF0 k
    · intro k t v ht
      apply hcoords k t v
      simpa [θ] using ht
  have actual_original_marked_half_disk_full_graph_clear_tapered_terminal_framed_band_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch)
      (h1 : D.secondCorner ∉ M.cover.branch)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (F : OpenPartialHomeomorph S Plane) (R : Interval × Icc (-1:ℝ) 1 → S),
        Disjoint F.source ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        D.secondCorner ∈ F.source ∧ F D.secondCorner=0 ∧
        (∀ x ∈ F.source,x ∈ (r0 ⟨u.val,hTF u.property⟩).val.image ↔ F x 1=0) ∧
        (∀ x ∈ F.source,x ∈ (rT u).val.image ↔ F x 0=0) ∧
        IsEmbedding R ∧ (∀ t,R (t,⟨0,by norm_num⟩)=D.firstSide t) ∧
      ∃ (σ δ η ρ : ℝ) (h : C(Interval,ℝ)),
        (σ = -1 ∨ σ=1) ∧ 0 < δ ∧ 0 < η ∧ 0 < ρ ∧ ρ ≤ 1/2 ∧ h 0=0 ∧
        (∀ t,0 ≤ h t ∧ h t ≤ ρ) ∧
        (∀ t : Interval,0 < (t:ℝ) → 0 < h t) ∧
        (∀ t : Interval,(1/2:ℝ) ≤ (t:ℝ) → h t=ρ) ∧
        (∀ (t : Interval) (v : Icc (-1:ℝ) 1),0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
          R (t,v) ∉ ((M.cover.branch : Set S) ∪ actualObjectTrace M r J)) ∧
        ∀ (t : Interval) (v : Icc (-1:ℝ) 1),|(t:ℝ)-1| < η →
          R (t,v) ∈ F.source ∧ F (R (t,v))=Plane.mk (F (D.firstSide t) 0) (σ*δ*(v:ℝ)) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨F,R,hF,hR,hcenter,σ,δ,η,hsign,hpos,hframe⟩ :=
      actual_original_marked_half_disk_terminal_crossing_framed_full_side_strip_private D h1 hcross
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    have hQ : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    have haxisFree (t : Interval) (ht : 0 < (t:ℝ)) : D.firstSide t ∉ Q := by
      intro hzQ
      have hm : D.firstSide t ∈ M.cover.branch :=
        actual_original_pair_closed_obstacle_contact_is_marked
          ⟨Or.inl (D.first_on_curve (mem_range_self t)),hzQ⟩
      have hzD : D.firstSide t ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show D.firstSide t ∈ range D.firstSide ∪ range D.secondSide from
          Or.inl (mem_range_self t)))
      rcases mem_insert_iff.mp (D.marks_are_corners _ hzD hm) with he | he
      · have htt : t=0 := D.first_embedded.injective (he.trans D.first_zero.symm)
        have hh := congrArg Subtype.val htt
        change (t:ℝ)=0 at hh
        exact ht.ne' hh
      · exact h1 ((mem_singleton_iff.mp he) ▸ hm)
    have haxis (t : Interval) (ht : 0 < (t:ℝ)) :
        D.firstSide ⟨(1:ℝ)*(t:ℝ),⟨mul_nonneg (by norm_num) t.property.1,
          (mul_le_of_le_one_right (by norm_num) t.property.2).trans (by norm_num)⟩⟩ ∉ Q := by
      simpa only [one_mul] using haxisFree t ht
    obtain ⟨ρ,hρ,hρhalf,h,hh0,hbound,hpositive,hflat,hband,g,hcoords,hg⟩ :=
      actual_embedded_side_given_strip_produces_graph_clear_full_base_taper_private
        D.firstSide R hR hcenter 1 (by norm_num) (by norm_num) Q hQ
        (Or.inl (D.first_zero.symm ▸ hbase)) haxis
    refine ⟨F (),R,(hF ()).1,?_,?_,(hF ()).2.2.2.1,(hF ()).2.2.2.2,hR,hcenter,
      σ (),δ (),η (),ρ,h,hsign (), (hpos ()).1,(hpos ()).2,hρ,hρhalf,hh0,hbound,
      hpositive,hflat,?_,?_⟩
    · exact D.first_one ▸ (hF ()).2.1
    · simpa only [D.first_one] using (hF ()).2.2.1
    · intro t v ht hv
      simpa only [one_mul] using hband t v ht hv
    · intro t v ht
      simpa only [] using hframe () t v ht
  have actual_embedded_side_strip_terminal_source_neighborhood_private
      (f : C(Interval,S)) (R : Interval × Icc (-1:ℝ) 1 → S)
      (hR : IsEmbedding R) (hcenter : ∀ t,R (t,⟨0,by norm_num⟩)=f t)
      (F : OpenPartialHomeomorph S Plane) (hp : f 1 ∈ F.source)
      (η : ℝ) (hη : 0 < η) :
      ∃ T : Set S, IsOpen T ∧ f 1 ∈ T ∧ T ⊆ F.source ∧
        ∀ (t : Interval) (v : Icc (-1:ℝ) 1),R (t,v) ∈ T → |(t:ℝ)-1|<η := by
    letI : T2Space S := M.sphere.symm.t2Space
    let Z := Interval × Icc (-1:ℝ) 1
    let Far : Set Z := {z | (z.1:ℝ) ≤ 1-η/2}
    have hFar : IsClosed Far := isClosed_le
      (continuous_subtype_val.comp continuous_fst) continuous_const
    have hFarC : IsCompact (R '' Far) := hFar.isCompact.image hR.continuous
    have hpFar : f 1 ∉ R '' Far := by
      rintro ⟨z,hz,he⟩
      have hzEq : z=(1,⟨0,by norm_num⟩) := hR.injective (he.trans (hcenter 1).symm)
      have hz1 : (z.1:ℝ)=1 := congrArg (fun z : Z => (z.1:ℝ)) hzEq
      change (z.1:ℝ) ≤ 1-η/2 at hz
      rw [hz1] at hz
      nlinarith
    let T : Set S := F.source ∩ (R '' Far)ᶜ
    refine ⟨T,F.open_source.inter hFarC.isClosed.isOpen_compl,⟨hp,hpFar⟩,
      inter_subset_left,?_⟩
    intro t v ht
    have htNear : 1-η/2 < (t:ℝ) := by
      by_contra hn
      exact ht.2 ⟨(t,v),le_of_not_gt hn,rfl⟩
    rw [abs_of_nonpos (sub_nonpos.mpr t.property.2)]
    nlinarith
  have actual_essential_subarc_outside_open_side_is_compact
      (a : EssentialMarkedArc M) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hfa : range f ⊆ a.val.image) :
      IsCompact (a.val.image \ (f '' Ioo (0:Interval) 1)) := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    have hopen := actual_essential_subarc_interior_isOpen a f hf hfa
    have hcl : IsClosed {x : a.val.image | (x:S) ∉ f '' Ioo (0:Interval) 1} :=
      hopen.isClosed_compl
    have heq : Subtype.val '' {x : a.val.image | (x:S) ∉ f '' Ioo (0:Interval) 1} =
        a.val.image \ (f '' Ioo (0:Interval) 1) := by
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        exact ⟨x.property,hx⟩
      · rintro ⟨ha,hf⟩
        exact ⟨⟨z,ha⟩,hf,rfl⟩
    have hclosed : IsClosed (a.val.image \ (f '' Ioo (0:Interval) 1)) := by
      rw [←heq]
      exact (isCompact_range a.val.continuous).isClosed.isClosedMap_subtype_val _ hcl
    exact hclosed.isCompact
  have actual_empty_marked_disk_first_side_clean_private
      (a b : EssentialMarkedArc M)
      (ht : ∀ p ∈ ArcSurgery.crossings M a b,ArcSurgery.CrossesInDisk M b a p)
      (B : ActualMarkedTwoSideDisk M a b)
      (hempty : Disjoint B.openInterior (a.val.image ∪ b.val.image)) :
      range B.firstSide ∩ b.val.image={B.firstCorner,B.secondCorner} := by
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
    apply Set.Subset.antisymm
    · rintro p ⟨hpf, hpb⟩
      by_contra hpnot
      have hpg : p ∉ Set.range B.secondSide := by
        intro h
        exact hpnot (B.sides_inter ▸ (show p ∈ Set.range B.firstSide ∩ Set.range B.secondSide from ⟨hpf,h⟩))
      have hpab : p ∈ a.val.image ∩ b.val.image := ⟨B.first_on_curve hpf,hpb⟩
      have hpBoundary' : p ∈ range B.disk := Set.image_subset_range _ _
        (B.boundary_eq.symm ▸ (show p ∈ range B.firstSide ∪ range B.secondSide from Or.inl hpf))
      have hnotmark : p ∉ M.cover.branch := fun hm => hpnot (B.marks_are_corners p hpBoundary' hm)
      obtain ⟨U,hU,hpU,hmarkfree,h,hpzero,hbaxis,haaxis⟩ := ht p ⟨⟨hpab.1,hnotmark⟩,hpab.2,hnotmark⟩
      let V : Set (ℝ × ℝ) := {q | |q.1| < 1 ∧ |q.2| < 1}
      have hV : IsOpen V :=
        (isOpen_lt (continuous_fst.abs) continuous_const).inter
          (isOpen_lt (continuous_snd.abs) continuous_const)
      have haxes (z : S) (hz : z ∈ U) :
          (z ∈ a.val.image ↔ (h ⟨z,hz⟩).val.1 = 0) ∧
          (z ∈ b.val.image ↔ (h ⟨z,hz⟩).val.2 = 0) := ⟨haaxis ⟨z,hz⟩,hbaxis ⟨z,hz⟩⟩
      have hgclosed : IsClosed (Set.range B.secondSide) :=
        by simpa only [Set.image_univ] using (isCompact_univ.image B.secondSide.continuous).isClosed
      let N : Set U := {x | (x : S) ∉ Set.range B.secondSide}
      have hN : IsOpen N := hgclosed.isOpen_compl.preimage continuous_subtype_val
      let O : Set (ℝ × ℝ) := Subtype.val '' (h '' N)
      have hO : IsOpen O := (hV.isOpenEmbedding_subtypeVal).isOpenMap _ (h.isOpenMap _ hN)
      have hzeroO : (0,0) ∈ O := ⟨h ⟨p,hpU⟩, ⟨⟨p,hpU⟩,hpg,rfl⟩,hpzero⟩
      obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hO (0,0) hzeroO
      have hpBoundary : p ∈ B.disk '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1} := by
        rw [B.boundary_eq]; exact Or.inl hpf
      obtain ⟨w, hw, hwp⟩ := hpBoundary
      have hwn : ‖w.val‖ = 1 := by
        simpa only [Set.mem_setOf_eq, Metric.mem_sphere, dist_zero_right] using hw
      let radial : C(Interval, Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
        ⟨fun t => ⟨t.val • w.val, by
          simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg t.property.1, hwn, mul_one]
          exact t.property.2⟩, by fun_prop⟩
      have honecl : (1 : Interval) ∈ closure (Set.Ioo (0 : Interval) 1) := by
        rw [closure_Ioo (by norm_num : (0 : Interval) ≠ 1)]
        exact ⟨by norm_num,le_rfl⟩
      have hpcl : p ∈ closure B.openInterior := by
        have hcl : (B.disk ∘ radial) '' closure (Set.Ioo (0 : Interval) 1) ⊆
            closure ((B.disk ∘ radial) '' Set.Ioo (0 : Interval) 1) :=
          image_closure_subset_closure_image (B.disk.continuous.comp radial.continuous)
        have him : (B.disk ∘ radial) '' Set.Ioo (0 : Interval) 1 ⊆ B.openInterior := by
          rintro z ⟨t,ht,rfl⟩
          refine ⟨radial t, ?_, rfl⟩
          change t.val • w.val ∈ Metric.ball 0 1
          simp only [Metric.mem_ball,dist_zero_right]
          simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg t.property.1,hwn,mul_one] using (show t.val < (1 : ℝ) from ht.2)
        apply closure_mono him
        apply hcl
        refine ⟨1,honecl,?_⟩
        change B.disk (radial 1) = p
        have hr : radial 1 = w := by apply Subtype.ext; simp [radial]
        rw [hr]; exact hwp
      let T := Metric.ball (0 : ℝ × ℝ) ε
      have hTV : T ⊆ V := by
        intro z hz
        obtain ⟨v,hv,he⟩ := hball hz
        exact he ▸ v.property
      let jV : T → V := fun z => ⟨z.val,hTV z.property⟩
      let j : C(T,S) := ⟨fun z => (h.symm (jV z)).val, by fun_prop⟩
      have hjopen : IsOpenMap j := hU.isOpenMap_subtype_val.comp
        (h.symm.isOpenMap.comp (Metric.isOpen_ball.isOpenMap_subtype_val.subtype_mk _))
      let zeroT : T := ⟨0,by change dist (0 : ℝ × ℝ) 0 < ε; simpa only [dist_self] using hε⟩
      have hjzero : j zeroT = p := by
        have heq : jV zeroT = h ⟨p,hpU⟩ := by apply Subtype.ext; exact hpzero.symm
        change (h.symm (jV zeroT)).val = p
        rw [heq,h.symm_apply_apply]
      have hjN (z : T) : j z ∉ Set.range B.secondSide := by
        obtain ⟨v,⟨u,hu,he⟩,hv⟩ := hball z.property
        have heq : jV z = h u := by apply Subtype.ext; exact hv.symm.trans (congrArg Subtype.val he).symm
        change (h.symm (jV z)).val ∉ _
        rw [heq,h.symm_apply_apply]
        exact hu
      let K := Set.range B.disk
      let J : Set T := j ⁻¹' B.openInterior
      have hJopen : IsOpen J := (LocalSurgery.embedded_surface_disk_interior_isOpen B.disk B.disk_embedded).preimage j.continuous
      have hzeroJcl : zeroT ∈ closure J := by
        apply hjopen.preimage_closure_subset_closure_preimage
        change j zeroT ∈ closure B.openInterior
        rwa [hjzero]
      have hKclosed : IsClosed K := by
        simpa only [Set.image_univ] using (isCompact_univ.image B.disk.continuous).isClosed
      have haxis (z : T) (hz : j z ∈ K) (hznot : z ∉ J) : z.val.1 = 0 := by
        obtain ⟨v,hv⟩ := hz
        have hn : ‖v.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using v.property
        have hnnot : ¬ ‖v.val‖ < 1 := by
          intro hnlt
          apply hznot
          exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hnlt,hv⟩
        have hb : j z ∈ Set.range B.firstSide ∪ Set.range B.secondSide := by
          rw [← B.boundary_eq]
          exact ⟨v,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using
            le_antisymm hn (le_of_not_gt hnnot),hv⟩
        have ha : j z ∈ a.val.image := B.first_on_curve (hb.resolve_right (hjN z))
        have hh := (haxes (j z) (h.symm (jV z)).property).1.mp ha
        have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
        simpa only [heq] using hh
      obtain ⟨z,hzall,hzJ⟩ := mem_closure_iff_nhds.mp hzeroJcl Set.univ (by simp)
      have hzaxis : z.val.1 ≠ 0 := by
        intro hz0
        have ha : j z ∈ a.val.image := (haxes (j z) (h.symm (jV z)).property).1.mpr (by
          have heq : h ⟨j z,(h.symm (jV z)).property⟩ = jV z := h.apply_symm_apply _
          simpa only [heq] using hz0)
        exact Set.disjoint_left.mp hempty hzJ (Or.inl ha)
      let σ : ℝ := z.val.1
      let H : Set T := {u | 0 < σ * u.val.1}
      have hzH : z ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
      let L : (ℝ × ℝ) →ₗ[ℝ] ℝ := σ • LinearMap.fst ℝ ℝ ℝ
      have hconv : Convex ℝ (T ∩ {u : ℝ × ℝ | 0 < σ * u.1}) :=
        (convex_ball (0 : ℝ × ℝ) ε).inter ((convex_Ioi (0 : ℝ)).linear_preimage L)
      have hHconn : _root_.IsPreconnected H := by
        apply IsInducing.subtypeVal.isPreconnected_image.mp
        have heq : Subtype.val '' H = T ∩ {u : ℝ × ℝ | 0 < σ * u.1} := by
          ext u
          constructor
          · rintro ⟨v,hv,rfl⟩; exact ⟨v.property,hv⟩
          · rintro ⟨hu,hv⟩; exact ⟨⟨u,hu⟩,hv,rfl⟩
        rw [heq]
        exact hconv.isPreconnected
      letI : PreconnectedSpace H := ⟨by
        apply IsInducing.subtypeVal.isPreconnected_image.mp
        simpa only [Set.image_univ,Subtype.range_val] using hHconn⟩
      let JH : Set H := Subtype.val ⁻¹' J
      have hJHeq : JH = (fun u : H => j u.val) ⁻¹' K := by
        ext u
        constructor
        · rintro ⟨v,hv,he⟩; exact ⟨v,he⟩
        · intro hu
          by_contra huJ
          have huaxis := haxis u.val hu huJ
          have hpos := u.property
          change 0 < σ * u.val.val.1 at hpos
          rw [huaxis,mul_zero] at hpos
          exact lt_irrefl 0 hpos
      have hJHclosed : IsClosed JH := by rw [hJHeq]; exact hKclosed.preimage (j.continuous.comp continuous_subtype_val)
      have hJHopen : IsOpen JH := hJopen.preimage continuous_subtype_val
      have hfull : JH = Set.univ := (show IsClopen JH from ⟨hJHclosed,hJHopen⟩).eq_univ
        ⟨⟨z,hzH⟩,hzJ⟩
      let e : T := ⟨(z.val.1,0),by
        have hzball := z.property
        change dist (z.val.1,0) (0 : ℝ × ℝ) < ε
        apply lt_of_le_of_lt ?_ hzball
        rw [Prod.dist_eq,Prod.dist_eq]
        change max (dist z.val.1 0) (dist (0 : ℝ) 0) ≤ max (dist z.val.1 0) (dist z.val.2 0)
        rw [dist_self]
        exact max_le_max le_rfl dist_nonneg⟩
      have heH : e ∈ H := by change 0 < z.val.1 * z.val.1; exact mul_self_pos.mpr hzaxis
      have heJ : e ∈ J := by
        have hm : (⟨e,heH⟩ : H) ∈ JH := hfull.symm ▸ Set.mem_univ _
        exact hm
      have heb : j e ∈ b.val.image := (haxes (j e) (h.symm (jV e)).property).2.mpr (by
        have heq : h ⟨j e,(h.symm (jV e)).property⟩ = jV e := h.apply_symm_apply _
        simpa only [heq] using (show e.val.2 = 0 from rfl))
      exact Set.disjoint_left.mp hempty heJ (Or.inr heb)
    · intro p hp
      rcases Set.mem_insert_iff.mp hp with hp | hp
      · subst p
        exact ⟨⟨0,B.first_zero⟩,B.second_on_curve ⟨0,B.second_zero⟩⟩
      · have hp' : p = B.secondCorner := Set.mem_singleton_iff.mp hp
        subst p
        exact ⟨⟨1,B.first_one⟩,B.second_on_curve ⟨1,B.second_one⟩⟩
  have actual_marked_side_base_tracks_avoid_entire_source_and_graph_private
      (a : EssentialMarkedArc M) (f : C(Interval,S)) (hf : IsEmbedding f)
      (hfa : range f ⊆ a.val.image) (G : Set S) (hG : IsClosed G)
      (hbase : f 0 ∈ M.cover.branch)
      (hfree : ∀ t : Interval, t ≠ 0 → f t ∉ M.cover.branch)
      (hgraph : range f ∩ G ⊆ (M.cover.branch : Set S)) :
      ∃ g : Bool → C(Interval,S), ∀ k,
        IsEmbedding (g k) ∧ g k 0=f 0 ∧
        range (g k) ∩ ((M.cover.branch : Set S) ∪ G ∪ a.val.image)={f 0} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let K : Set S := a.val.image \ (f '' Ioo (0:Interval) 1)
    have hK : IsCompact K := actual_essential_subarc_outside_open_side_is_compact a f hf hfa
    let P : Set S := ((M.cover.branch : Set S) ∪ G) ∪ K
    have hP : IsClosed P := (M.cover.branch.finite_toSet.isClosed.union hG).union hK.isClosed
    have hbP : f 0 ∈ P := Or.inl (Or.inl hbase)
    have haxis (t : Interval) (ht : 0 < (t:ℝ)) :
        f ⟨(1/2:ℝ)*(t:ℝ),⟨mul_nonneg (by norm_num) t.property.1,
          (mul_le_of_le_one_right (by norm_num) t.property.2).trans (by norm_num)⟩⟩ ∉ P := by
      let u : Interval := ⟨(1/2:ℝ)*(t:ℝ),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
      have hu0 : (0:Interval) < u := by change 0 < (1/2:ℝ)*(t:ℝ); positivity
      have hu1 : u < (1:Interval) := by change (1/2:ℝ)*(t:ℝ)<1; nlinarith [t.property.2]
      have hnm : f u ∉ M.cover.branch := hfree u (ne_of_gt hu0)
      change f u ∉ P
      intro hz
      rcases hz with (hm | hg) | hk
      · exact hnm hm
      · exact hnm (hgraph ⟨mem_range_self u,hg⟩)
      · exact hk.2 ⟨u,⟨hu0,hu1⟩,rfl⟩
    obtain ⟨E,hE,hcenter,ρ,hρ,hρhalf,h,hh0,hbound,hpos,htail,hband,g,hcoords,hg⟩ :=
      actual_embedded_marked_side_produces_base_vanishing_tracks_private
        f hf (1/2) (by norm_num) (by norm_num) P hP hbP haxis
    refine ⟨g,?_⟩
    intro k
    refine ⟨(hg k).1,(hg k).2.1,?_⟩
    ext z
    constructor
    · rintro ⟨hz,hzObstacle⟩
      have hzP_or_side : z ∈ P ∨ z ∈ range f := by
        rcases hzObstacle with (hm | hgraph) | ha
        · exact Or.inl (Or.inl (Or.inl hm))
        · exact Or.inl (Or.inl (Or.inr hgraph))
        · by_cases hside : z ∈ f '' Ioo (0:Interval) 1
          · exact Or.inr (image_subset_range _ _ hside)
          · exact Or.inl (Or.inr ⟨ha,hside⟩)
      rcases hzP_or_side with hzP | hzSide
      · exact (hg k).2.2.1 ▸ ⟨hz,hzP⟩
      · exact (hg k).2.2.2 ▸ ⟨hz,hzSide⟩
    · intro hz
      have he := mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨0,(hg k).2.1⟩,Or.inl (Or.inl hbase)⟩
  have actual_original_marked_half_disk_produces_base_tracks_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch)
      (hterminal : D.secondCorner ∉ M.cover.branch) :
      ∃ g : Bool → C(Interval,S), ∀ k,
        IsEmbedding (g k) ∧ g k 0=D.firstCorner ∧
        range (g k) ∩ ((M.cover.branch : Set S) ∪ actualObjectTrace M r J ∪
          (r0 ⟨u.val,hTF u.property⟩).val.image)={D.firstCorner} := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hfree (t : Interval) (ht : t ≠ 0) : D.firstSide t ∉ M.cover.branch := by
      intro hm
      have htD : D.firstSide t ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show D.firstSide t ∈ range D.firstSide ∪ range D.secondSide from
          Or.inl (mem_range_self t)))
      rcases mem_insert_iff.mp (D.marks_are_corners _ htD hm) with he | he
      · exact ht (D.first_embedded.injective (he.trans D.first_zero.symm))
      · exact hterminal ((mem_singleton_iff.mp he) ▸ hm)
    have hgraph : range D.firstSide ∩ actualObjectTrace M r J ⊆ (M.cover.branch : Set S) := by
      rintro z ⟨hz,hzG⟩
      exact actual_original_pair_entire_graph_contact_is_marked ⟨Or.inl (D.first_on_curve hz),hzG⟩
    obtain ⟨g,hg⟩ := actual_marked_side_base_tracks_avoid_entire_source_and_graph_private
      (r0 ⟨u.val,hTF u.property⟩) D.firstSide D.first_embedded D.first_on_curve
      (actualObjectTrace M r J) (actualObjectTrace_compact M r J).isClosed
      (D.first_zero.symm ▸ hbase) hfree hgraph
    refine ⟨g,?_⟩
    intro k
    simpa only [D.first_zero] using hg k
  have actual_original_marked_half_disk_produces_entire_pair_graph_clear_base_tracks_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch)
      (hterminal : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ g : Bool → C(Interval,S), ∀ k,
        IsEmbedding (g k) ∧ g k 0=D.firstCorner ∧
        range (g k) ∩ (((M.cover.branch : Set S) ∪ actualObjectTrace M r J ∪
          (rT u).val.image) ∪ (r0 ⟨u.val,hTF u.property⟩).val.image)={D.firstCorner} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    let q : Interval → Interval := fun t => ⟨(1/2:ℝ)*(t:ℝ),by
      constructor <;> nlinarith [t.property.1,t.property.2]⟩
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hqi : Function.Injective q := by
      intro t s he
      apply Subtype.ext
      have hh := congrArg Subtype.val he
      change (1/2:ℝ)*(t:ℝ)=(1/2:ℝ)*(s:ℝ) at hh
      nlinarith
    let f : C(Interval,S) := ⟨D.firstSide ∘ q,D.firstSide.continuous.comp hq⟩
    have hf : IsEmbedding f := (f.continuous.isClosedEmbedding
      (D.first_embedded.injective.comp hqi)).isEmbedding
    have hf0 : f 0=D.firstCorner := by
      change D.firstSide (q 0)=D.firstCorner
      have hh : q 0=0 := by apply Subtype.ext; simp [q]
      rw [hh,D.first_zero]
    have hfa : range f ⊆ a.val.image := by
      rintro z ⟨t,rfl⟩
      exact D.first_on_curve (mem_range_self (q t))
    have hclean : range D.firstSide ∩ b.val.image={D.firstCorner,D.secondCorner} :=
      actual_empty_marked_disk_first_side_clean_private a b
        (fun p hp => actual_marked_crossesInDisk_symm M a b p (hcross p hp)) D hempty
    have hfree (t : Interval) (ht : t ≠ 0) : f t ∉ M.cover.branch := by
      intro hm
      have htD : f t ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show f t ∈ range D.firstSide ∪ range D.secondSide from
          Or.inl (mem_range_self (q t))))
      rcases mem_insert_iff.mp (D.marks_are_corners _ htD hm) with he | he
      · exact ht (hqi (D.first_embedded.injective (he.trans hf0.symm)))
      · exact hterminal ((mem_singleton_iff.mp he) ▸ hm)
    let G : Set S := actualObjectTrace M r J ∪ b.val.image
    have hbclosed : IsClosed b.val.image := by
      simpa only [Set.image_univ,MarkedArc.image] using (isCompact_univ.image b.val.continuous).isClosed
    have hG : IsClosed G := (actualObjectTrace_compact M r J).isClosed.union hbclosed
    have hgraph : range f ∩ G ⊆ (M.cover.branch : Set S) := by
      rintro z ⟨⟨t,rfl⟩,hzG⟩
      rcases hzG with hzGraph | hzB
      · exact actual_original_pair_entire_graph_contact_is_marked ⟨Or.inl (hfa (mem_range_self t)),hzGraph⟩
      · have hh : f t ∈ ({D.firstCorner,D.secondCorner}:Set S) :=
          hclean ▸ ⟨mem_range_self (q t),hzB⟩
        rcases mem_insert_iff.mp hh with he | he
        · exact he.symm ▸ hbase
        · have ht1 : q t=1 := D.first_embedded.injective ((mem_singleton_iff.mp he).trans D.first_one.symm)
          have hh := congrArg Subtype.val ht1
          change (1/2:ℝ)*(t:ℝ)=1 at hh
          exact False.elim (by nlinarith [t.property.2])
    obtain ⟨g,hg⟩ := actual_marked_side_base_tracks_avoid_entire_source_and_graph_private
      a f hf hfa G hG (hf0.symm ▸ hbase) hfree hgraph
    refine ⟨g,?_⟩
    intro k
    simpa only [G,a,b,hf0,Set.union_assoc] using hg k
  have actual_original_marked_half_disk_rounded_side_closed_obstacle_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch)
      (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p)
      (T : Set S) (hT : IsOpen T) (hpT : D.secondCorner ∈ T) :
      ∃ P : Set S,
        P=(((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∪
          (((r0 ⟨u.val,hTF u.property⟩).val.image \ (D.firstSide '' Ioo (0:Interval) 1)) ∩ Tᶜ)) ∪
          ((rT u).val.image ∩ Tᶜ) ∧
        IsClosed P ∧ D.firstSide 0 ∈ P ∧
        ∀ t : Interval,0 < (t:ℝ) → D.firstSide t ∉ P := by
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    let Q : Set S := (M.cover.branch : Set S) ∪ actualObjectTrace M r J
    let K : Set S := a.val.image \ (D.firstSide '' Ioo (0:Interval) 1)
    let P : Set S := (Q ∪ (K ∩ Tᶜ)) ∪ (b.val.image ∩ Tᶜ)
    have hK : IsCompact K := actual_essential_subarc_outside_open_side_is_compact
      a D.firstSide D.first_embedded D.first_on_curve
    have hb : IsClosed b.val.image := by
      simpa only [Set.image_univ,MarkedArc.image] using (isCompact_univ.image b.val.continuous).isClosed
    have hQ : IsClosed Q := M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed
    have hclean : range D.firstSide ∩ b.val.image={D.firstCorner,D.secondCorner} :=
      actual_empty_marked_disk_first_side_clean_private a b
        (fun p hp => actual_marked_crossesInDisk_symm M a b p (hcross p hp)) D hempty
    refine ⟨P,rfl,(hQ.union (hK.isClosed.inter hT.isClosed_compl)).union
      (hb.inter hT.isClosed_compl),Or.inl (Or.inl (Or.inl (D.first_zero.symm ▸ hbase))),?_⟩
    intro t ht hz
    have ht0 : t ≠ 0 := by
      intro he
      have hh := congrArg Subtype.val he
      change (t:ℝ)=0 at hh
      exact ht.ne' hh
    have hnotBase : D.firstSide t ≠ D.firstCorner := by
      intro he
      exact ht0 (D.first_embedded.injective (he.trans D.first_zero.symm))
    rcases hz with (hzQ | hzK) | hzB
    · have hm : D.firstSide t ∈ M.cover.branch :=
        actual_original_pair_closed_obstacle_contact_is_marked
          ⟨Or.inl (D.first_on_curve (mem_range_self t)),hzQ⟩
      have hzD : D.firstSide t ∈ range D.disk := image_subset_range _ _
        (D.boundary_eq.symm ▸ (show D.firstSide t ∈ range D.firstSide ∪ range D.secondSide from
          Or.inl (mem_range_self t)))
      rcases mem_insert_iff.mp (D.marks_are_corners _ hzD hm) with he | he
      · exact hnotBase he
      · exact h1 ((mem_singleton_iff.mp he) ▸ hm)
    · by_cases ht1 : t=1
      · exact hzK.2 (ht1 ▸ D.first_one.symm ▸ hpT)
      · exact hzK.1.2 ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
    · have hh : D.firstSide t ∈ ({D.firstCorner,D.secondCorner}:Set S) :=
        hclean ▸ ⟨mem_range_self t,hzB.1⟩
      rcases mem_insert_iff.mp hh with he | he
      · exact hnotBase he
      · exact hzB.2 ((mem_singleton_iff.mp he).symm ▸ hpT)
  have actual_essential_terminal_rail_old_side_dichotomy_private
      (b : EssentialMarkedArc M) (f n : C(Interval,S))
      (hf : IsEmbedding f) (hn : IsEmbedding n)
      (hfb : range f ⊆ b.val.image) (hnb : range n ⊆ b.val.image)
      (hbase : f 0 ∈ M.cover.branch) (hn0 : n 0=f 1)
      (hnfree : ∀ t,n t ∉ M.cover.branch) :
      range n ⊆ range f ∨ range n ∩ range f={f 1} := by
    letI : T2Space S := M.sphere.symm.t2Space
    let X := Ioc (0:Interval) 1
    letI : ConnectedSpace X := Subtype.connectedSpace
      (isConnected_Ioc (by norm_num : (0:Interval)<1))
    let A : Set X := {t | n t.val ∈ range f}
    let N : X → b.val.image := fun t => ⟨n t.val,hnb (mem_range_self t.val)⟩
    have hN : Continuous N := ((n.continuous.comp continuous_subtype_val).subtype_mk _)
    let B : Set b.val.image := {z | (z:S) ∈ f '' Ioo (0:Interval) 1}
    have hB : IsOpen B := actual_essential_subarc_interior_isOpen b f hf hfb
    have hAeq : A=N ⁻¹' B := by
      ext t
      constructor
      · rintro ⟨s,he⟩
        have hs0 : s ≠ 0 := by
          intro hs
          exact hnfree t.val ((he.symm.trans (congrArg f hs)).symm ▸ hbase)
        have hs1 : s ≠ 1 := by
          intro hs
          have htt : t.val=0 := hn.injective ((he.symm.trans (congrArg f hs)).trans hn0.symm)
          exact t.property.1.ne' htt
        exact ⟨s,⟨lt_of_le_of_ne (show (0:Interval) ≤ s from s.property.1) (Ne.symm hs0),
          lt_of_le_of_ne (show s ≤ (1:Interval) from s.property.2) hs1⟩,he⟩
      · intro ht
        exact image_subset_range f _ ht
    have hAc : IsClosed A := (isCompact_range f.continuous).isClosed.preimage
      (n.continuous.comp continuous_subtype_val)
    have hAo : IsOpen A := by rw [hAeq]; exact hB.preimage hN
    by_cases hne : A.Nonempty
    · have hall : A=univ := (show IsClopen A from ⟨hAc,hAo⟩).eq_univ hne
      left
      rintro z ⟨t,rfl⟩
      by_cases ht : t=0
      · exact ⟨1,(congrArg n ht).trans hn0 |>.symm⟩
      · have hx : t ∈ Ioc (0:Interval) 1 :=
          ⟨lt_of_le_of_ne (show (0:Interval) ≤ t from t.property.1) (Ne.symm ht),t.property.2⟩
        have htA : (⟨t,hx⟩:X) ∈ A := hall.symm ▸ (show (⟨t,hx⟩:X) ∈ univ from mem_univ _)
        exact htA
    · right
      ext z
      constructor
      · rintro ⟨⟨t,ht⟩,hzf⟩
        have ht0 : t=0 := by
          by_contra hnz
          have hx : t ∈ Ioc (0:Interval) 1 :=
            ⟨lt_of_le_of_ne (show (0:Interval) ≤ t from t.property.1) (Ne.symm hnz),t.property.2⟩
          have hzn : n t ∈ range f := ht.symm ▸ hzf
          exact hne ⟨⟨t,hx⟩,hzn⟩
        exact mem_singleton_iff.mpr (ht.symm.trans ((congrArg n ht0).trans hn0))
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,hn0⟩,mem_range_self 1⟩
  have actual_two_terminal_rails_not_both_inside_embedded_old_side_private
      (f : C(Interval,S)) (hf : IsEmbedding f) (n : Bool → C(Interval,S))
      (hn : ∀ k,IsEmbedding (n k)) (hstart : ∀ k,n k 0=f 1)
      (hinter : range (n false) ∩ range (n true)={f 1}) :
      ¬ (range (n false) ⊆ range f ∧ range (n true) ⊆ range f) := by
    intro hboth
    have hon (k : Bool) : range (n k) ⊆ range f := by cases k; exact hboth.1; exact hboth.2
    let q : Bool → Interval → Interval := fun k t =>
      hf.toHomeomorph.symm ⟨n k t,hon k (mem_range_self t)⟩
    have hq (k : Bool) : Continuous (q k) := hf.toHomeomorph.symm.continuous.comp
      ((n k).continuous.subtype_mk _)
    have hqmap (k : Bool) (t : Interval) : f (q k t)=n k t :=
      congrArg Subtype.val (hf.toHomeomorph.apply_symm_apply ⟨n k t,hon k (mem_range_self t)⟩)
    have hq0 (k : Bool) : q k 0=1 := hf.injective ((hqmap k 0).trans (hstart k))
    have hq1ne (k : Bool) : q k 1 ≠ 1 := by
      intro he
      have hn10 : n k 1=n k 0 := (hqmap k 1).symm.trans
        ((congrArg f he).trans (hstart k).symm)
      exact one_ne_zero ((hn k).injective hn10)
    have hq1lt (k : Bool) : (q k 1:ℝ)<1 := lt_of_le_of_ne (q k 1).property.2
      (fun he => hq1ne k (Subtype.ext he))
    let m : ℝ := (max (q false 1:ℝ) (q true 1:ℝ)+1)/2
    have hmax : max (q false 1:ℝ) (q true 1:ℝ)<1 := max_lt (hq1lt false) (hq1lt true)
    have hmlo : max (q false 1:ℝ) (q true 1:ℝ)< m := by dsimp [m]; linarith
    have hmhi : m<1 := by dsimp [m]; linarith
    have hm0 : 0 ≤ m := (q false 1).property.1.trans ((le_max_left _ _).trans hmlo.le)
    have hpre (k : Bool) : ∃ t : Interval,(q k t:ℝ)=m := by
      have hklo : (q k 1:ℝ) ≤ m := by
        cases k
        · exact (le_max_left _ _).trans hmlo.le
        · exact (le_max_right _ _).trans hmlo.le
      have hreal : Continuous (fun t : Interval => (q k t:ℝ)) := continuous_subtype_val.comp (hq k)
      have hm : m ∈ Icc (q k 1:ℝ) (q k 0:ℝ) := by
        rw [hq0 k]
        exact ⟨hklo,hmhi.le⟩
      obtain ⟨t,ht,hqt⟩ := intermediate_value_Icc'
        (by norm_num : (0:Interval) ≤ 1) hreal.continuousOn hm
      exact ⟨t,hqt⟩
    obtain ⟨t,ht⟩ := hpre false
    obtain ⟨u,hu⟩ := hpre true
    have hqu : q false t=q true u := Subtype.ext (ht.trans hu.symm)
    have hnEq : n false t=n true u := (hqmap false t).symm.trans
      ((congrArg f hqu).trans (hqmap true u))
    have hz : n false t=f 1 := mem_singleton_iff.mp
      (hinter ▸ (show n false t ∈ range (n false) ∩ range (n true) from
        ⟨mem_range_self t,⟨u,hnEq.symm⟩⟩))
    have hqEq : q false t=1 := hf.injective ((hqmap false t).trans hz)
    have hrealEq := congrArg Subtype.val hqEq
    change (q false t:ℝ)=1 at hrealEq
    exact hmhi.ne (ht.symm.trans hrealEq)
  have actual_embedded_side_band_into_actual_puncture_private
      (A : C(Interval,S)) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
      (N : Interval × Icc (-1:ℝ) 1 → S) (hN : IsEmbedding N)
      (hcenter : ∀ t, N (t,⟨0,by norm_num⟩)=A t)
      (ρ : ℝ) (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2)
      (h : C(Interval,ℝ)) (hh0 : h 0=0) (hh1 : h 1=ρ)
      (hbound : ∀ t, 0 ≤ h t ∧ h t ≤ ρ)
      (P : Set S) (hmarks : (M.cover.branch : Set S) ⊆ P)
      (hband : ∀ (t : Interval) (v : Icc (-1:ℝ) 1), 0 < (t:ℝ) → |(v:ℝ)| ≤ h t →
        N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
          (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩,v) ∉ P)
      (s : Bool) :
      ∃ F : C(Interval × Interval,↥(((M.cover.branch : Set S) \ {A 0})ᶜ)),
        (∀ (t : Interval), (F (t,0):S)=A
          ⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩) ∧
        (∀ (w : Interval), (F (0,w):S)=A 0) ∧
        ∀ (t w : Interval), ∃ v : Icc (-1:ℝ) 1,
          (v:ℝ)=(if s then (1:ℝ) else -1)*h t*(w:ℝ) ∧
          (F (t,w):S)=N (⟨β*(t:ℝ),⟨mul_nonneg hβ0.le t.property.1,
            (mul_le_of_le_one_right hβ0.le t.property.2).trans hβ1⟩⟩,v) := by
    let sign : ℝ := if s then 1 else -1
    have habs : |sign|=1 := by cases s <;> norm_num [sign]
    let v : Interval × Interval → Icc (-1:ℝ) 1 := fun x => ⟨sign*h x.1*(x.2:ℝ),by
      apply abs_le.mp
      rw [abs_mul,abs_mul,habs,one_mul,abs_of_nonneg (hbound x.1).1,abs_of_nonneg x.2.property.1]
      have hh : h x.1*(x.2:ℝ) ≤ h x.1 := mul_le_of_le_one_right (hbound x.1).1 x.2.property.2
      exact hh.trans ((hbound x.1).2.trans (hρhalf.trans (by norm_num)))⟩
    let L : Interval × Interval → Interval × Icc (-1:ℝ) 1 := fun x =>
      (⟨β*(x.1:ℝ),⟨mul_nonneg hβ0.le x.1.property.1,
        (mul_le_of_le_one_right hβ0.le x.1.property.2).trans hβ1⟩⟩,v x)
    have hL : Continuous L := by dsimp [L,v]; fun_prop
    have hvbound (t w : Interval) : |(v (t,w):ℝ)| ≤ h t := by
      change |sign*h t*(w:ℝ)| ≤ h t
      rw [abs_mul,abs_mul,habs,one_mul,abs_of_nonneg (hbound t).1,abs_of_nonneg w.property.1]
      exact mul_le_of_le_one_right (hbound t).1 w.property.2
    have hbase (w : Interval) : N (L (0,w))=A 0 := by
      have hL0 : L (0,w)=(0,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · apply Subtype.ext; dsimp [L]; norm_num
        · apply Subtype.ext; dsimp [L,v]; rw [hh0]; simp
      rw [hL0,hcenter]
    have hX (x : Interval × Interval) : N (L x) ∈ (((M.cover.branch : Set S) \ {A 0})ᶜ) := by
      by_cases hx : x.1=0
      · have he := hbase x.2
        rw [show L x=L (0,x.2) from congrArg L (Prod.ext hx rfl),he]
        simp
      · intro hm
        exact hband x.1 (v x) (lt_of_le_of_ne x.1.property.1 (Ne.symm (by intro he; exact hx (Subtype.ext he))))
          (hvbound _ _) (hmarks hm.1)
    let F : C(Interval × Interval,↥(((M.cover.branch : Set S) \ {A 0})ᶜ)) :=
      ⟨fun x => ⟨N (L x),hX x⟩,(hN.continuous.comp hL).subtype_mk _⟩
    refine ⟨F,?_,hbase,fun t w => ⟨v (t,w),rfl,rfl⟩⟩
    intro t
    have hv0 : v (t,0)=⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [v]; simp
    change N (L (t,0)) = _
    dsimp only [L]
    rw [hv0,hcenter]
  have actual_square_boundary_path_homotopy_private {Y : Type} [TopologicalSpace Y]
      (F : C(Interval × Interval,Y)) :
      ∃ (α : Path (F (0,1)) (F (1,1))) (δ : Path (F (0,1)) (F (0,0)))
        (b : Path (F (0,0)) (F (1,0))) (v : Path (F (1,0)) (F (1,1))),
        (∀ t, α t=F (t,1)) ∧ (∀ t, δ t=F (0,unitInterval.symm t)) ∧
        (∀ t, b t=F (t,0)) ∧ (∀ t, v t=F (1,t)) ∧
        α.Homotopic (δ.trans (b.trans v)) := by
    let top : Path ((0,1) : Interval × Interval) (1,1) :=
      ⟨⟨fun t => (t,1),by fun_prop⟩,rfl,rfl⟩
    let left : Path ((0,1) : Interval × Interval) (0,0) :=
      ⟨⟨fun t => (0,unitInterval.symm t),by fun_prop⟩,by simp,by simp⟩
    let bottom : Path ((0,0) : Interval × Interval) (1,0) :=
      ⟨⟨fun t => (t,0),by fun_prop⟩,rfl,rfl⟩
    let right : Path ((1,0) : Interval × Interval) (1,1) :=
      ⟨⟨fun t => (1,t),by fun_prop⟩,rfl,rfl⟩
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
    have hhom := (SimplyConnectedSpace.paths_homotopic top (left.trans (bottom.trans right))).map F
    refine ⟨top.map F.continuous,left.map F.continuous,bottom.map F.continuous,right.map F.continuous,
      (fun _ => rfl),(fun _ => rfl),(fun _ => rfl),(fun _ => rfl),?_⟩
    simpa only [Path.map_trans] using hhom
  have actual_based_square_boundary_path_homotopy_private {Y : Type} [TopologicalSpace Y]
      (F : C(Interval × Interval,Y)) (p : Y) (hleft : ∀ w, F (0,w)=p) :
      ∃ (α : Path p (F (1,1))) (b : Path p (F (1,0)))
        (v : Path (F (1,0)) (F (1,1))),
        (∀ t, α t=F (t,1)) ∧ (∀ t, b t=F (t,0)) ∧
        (∀ t, v t=F (1,t)) ∧ α.Homotopic (b.trans v) := by
    obtain ⟨α,δ,b,v,hα,hδ,hb,hv,hhom⟩ := actual_square_boundary_path_homotopy_private F
    let α' := α.cast (hleft 1).symm rfl
    let b' := b.cast (hleft 0).symm rfl
    let δ' := δ.cast (hleft 1).symm (hleft 0).symm
    have hδ' : δ'=Path.refl p := by
      apply Path.ext
      funext t
      exact (hδ t).trans (hleft _)
    have hc : (δ.trans (b.trans v)).cast (hleft 1).symm rfl =
        δ'.trans (b'.trans v) := by
      exact Path.cast_trans δ (b.trans v) (hleft 1).symm (hleft 0).symm rfl
    have hh := hhom.pathCast (hleft 1).symm rfl
    rw [hc,hδ'] at hh
    exact ⟨α',b',v,hα,hb,hv,hh.trans (Path.Homotopic.refl_trans (b'.trans v))⟩
  have actual_original_half_disk_sides_punctured_homotopy_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hlast : D.secondCorner ∉ M.cover.branch) :
      ∃ (hp : D.firstCorner ∈ ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ)
        (hq : D.secondCorner ∈ ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ),
      ∃ α β : Path (⟨D.firstCorner,hp⟩ : ↑(((M.cover.branch : Set S) \ {D.firstCorner})ᶜ)) ⟨D.secondCorner,hq⟩,
        (∀ t, (α t : S)=D.firstSide t) ∧ (∀ t, (β t : S)=D.secondSide t) ∧ α.Homotopic β := by
    let X : Set S := ((M.cover.branch : Set S) \ {D.firstCorner})ᶜ
    let K := Metric.closedBall (0 : Plane) 1
    have hX (y : S) (hy : y ∈ range D.disk) : y ∈ X := by
      rintro ⟨hym,hyne⟩
      have hym' : y ∈ M.cover.branch := hym
      rcases mem_insert_iff.mp (D.marks_are_corners y hy hym') with he | he
      · exact hyne he
      · exact hlast ((mem_singleton_iff.mp he) ▸ hym')
    have hp : D.firstCorner ∈ X := by simp [X]
    have hq : D.secondCorner ∈ X := by
      intro hy
      exact hlast hy.1
    let F : C(K,X) := ⟨fun x => ⟨D.disk x,hX _ (mem_range_self x)⟩,
      D.disk.continuous.subtype_mk _⟩
    have hfirst (t : Interval) : D.firstSide t ∈ range D.disk := by
      apply image_subset_range D.disk _
      rw [D.boundary_eq]; exact Or.inl (mem_range_self t)
    have hsecond (t : Interval) : D.secondSide t ∈ range D.disk := by
      apply image_subset_range D.disk _
      rw [D.boundary_eq]; exact Or.inr (mem_range_self t)
    let e := D.disk_embedded.toHomeomorph
    let f : C(Interval,K) := ⟨fun t => e.symm ⟨D.firstSide t,hfirst t⟩,
      e.symm.continuous.comp (D.firstSide.continuous.subtype_mk _)⟩
    let g : C(Interval,K) := ⟨fun t => e.symm ⟨D.secondSide t,hsecond t⟩,
      e.symm.continuous.comp (D.secondSide.continuous.subtype_mk _)⟩
    have hf (t : Interval) : D.disk (f t)=D.firstSide t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨D.firstSide t,hfirst t⟩)
    have hg (t : Interval) : D.disk (g t)=D.secondSide t :=
      congrArg Subtype.val (e.apply_symm_apply ⟨D.secondSide t,hsecond t⟩)
    let α₀ : Path (f 0) (f 1) := ⟨f,rfl,rfl⟩
    let β₀ : Path (f 0) (f 1) := ⟨g,
      D.disk_embedded.injective ((hg 0).trans (D.second_zero.trans (D.first_zero.symm.trans (hf 0).symm))),
      D.disk_embedded.injective ((hg 1).trans (D.second_one.trans (D.first_one.symm.trans (hf 1).symm)))⟩
    letI : ContractibleSpace K := (convex_closedBall (0 : Plane) 1).contractibleSpace ⟨0,by simp⟩
    have hhom := (SimplyConnectedSpace.paths_homotopic α₀ β₀).map F
    have hsource : (⟨D.firstCorner,hp⟩ : X)=F (f 0) :=
      Subtype.ext ((hf 0).trans D.first_zero).symm
    have htarget : (⟨D.secondCorner,hq⟩ : X)=F (f 1) :=
      Subtype.ext ((hf 1).trans D.first_one).symm
    refine ⟨hp,hq,(α₀.map F.continuous).cast hsource htarget,
      (β₀.map F.continuous).cast hsource htarget,?_,?_,hhom.pathCast hsource htarget⟩
    · exact hf
    · exact hg
  have actual_original_marked_half_disk_two_rounded_whole_trace_clear_sides_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ g n : Bool → C(Interval,S),
        range (n false) ∩ range (n true)={D.secondCorner} ∧ ∀ k,
        IsEmbedding (g k) ∧ g k 0=D.firstCorner ∧
        range (g k) ∩ (r0 ⟨u.val,hTF u.property⟩).val.image={D.firstCorner} ∧
        range (g k) ∩ (rT u).val.image={D.firstCorner,g k 1} ∧
        range (g k) ∩ ((M.cover.branch : Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        g k 1 ∉ M.cover.branch ∧ IsEmbedding (n k) ∧ n k 0=D.secondCorner ∧
        n k 1=g k 1 ∧ range (n k) ⊆ (rT u).val.image ∧
        Disjoint (range (n k)) ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        ∃ (hp : D.firstCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hq : D.secondCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hz : g k 1 ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ),
        ∃ (rail : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g k 1,hz⟩)
          (side : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨D.secondCorner,hq⟩)
          (normal : Path (⟨D.secondCorner,hq⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g k 1,hz⟩),
          (∀ t,(rail t:S)=g k t) ∧ (∀ t,(side t:S)=D.secondSide t) ∧
          (∀ t,(normal t:S)=n k t) ∧ rail.Homotopic (side.trans normal) := by
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨F,R,hF,hR,hcenter,σ,δ,η,hsign,hpos,hframe⟩ :=
      actual_original_marked_half_disk_terminal_crossing_framed_full_side_strip_private D h1 hcross
    obtain ⟨T,hT,hpT,hTF,hTframe⟩ :=
      actual_embedded_side_strip_terminal_source_neighborhood_private D.firstSide R hR hcenter
        (F ()) (hF ()).2.1 (η ()) (hpos ()).2
    have hpT' : D.secondCorner ∈ T := D.first_one ▸ hpT
    obtain ⟨P,hPeq,hP,hbP,haxisFree⟩ :=
      actual_original_marked_half_disk_rounded_side_closed_obstacle_private
        D hbase h1 hempty hcross T hT hpT'
    have haxis (t : Interval) (ht : 0 < (t:ℝ)) :
        D.firstSide ⟨(1:ℝ)*(t:ℝ),⟨mul_nonneg (by norm_num) t.property.1,
          (mul_le_of_le_one_right (by norm_num) t.property.2).trans (by norm_num)⟩⟩ ∉ P := by
      simpa only [one_mul] using haxisFree t ht
    obtain ⟨ρ,hρ,hρhalf,h,hh0,hbound,hpositive,hflat,hband,g,hcoords,hg⟩ :=
      actual_embedded_side_given_strip_produces_graph_clear_full_base_taper_private
        D.firstSide R hR hcenter 1 (by norm_num) (by norm_num) P hP hbP haxis
    have hg0 (k : Bool) : g k 0=D.firstCorner := (hg k).2.1.trans D.first_zero
    have havoidP (k : Bool) (t : Interval) (ht : 0 < (t:ℝ)) : g k t ∉ P := by
      intro hz
      have he : g k t=D.firstSide 0 := mem_singleton_iff.mp
        ((hg k).2.2.1 ▸ (show g k t ∈ range (g k) ∩ P from ⟨mem_range_self t,hz⟩))
      have ht0 : t=0 := (hg k).1.injective (he.trans (hg k).2.1.symm)
      have hh := congrArg Subtype.val ht0
      change (t:ℝ)=0 at hh
      exact ht.ne' hh
    have hcoords' (k : Bool) (t : Interval) :
        ∃ v : Icc (-1:ℝ) 1,(v:ℝ)=(if k then (1:ℝ) else -1)*h t ∧ g k t=R (t,v) := by
      simpa only [one_mul] using hcoords k t
    have hσne : σ () ≠ 0 := by rcases hsign () with he | he <;> rw [he] <;> norm_num
    have hrealpos (t : Interval) (ht : t ≠ 0) : 0 < (t:ℝ) :=
      lt_of_le_of_ne t.property.1 (Ne.symm (fun he => ht (Subtype.ext he)))
    have hclearA (k : Bool) (t : Interval) (ht : 0 < (t:ℝ)) : g k t ∉ a.val.image := by
      intro hza
      obtain ⟨v,hv,hgv⟩ := hcoords' k t
      have hvne : (v:ℝ) ≠ 0 := by
        rw [hv]
        cases k <;> simp [ne_of_gt (hpositive t ht)]
      by_cases hzT : g k t ∈ T
      · have hnear := hTframe t v (hgv ▸ hzT)
        have hfr := hframe () t v hnear
        have hzF : g k t ∈ (F ()).source := hTF hzT
        have hzaxis := ((hF ()).2.2.2.1 _ hzF).mp hza
        rw [hgv,hfr.2] at hzaxis
        change σ ()*δ ()*(v:ℝ)=0 at hzaxis
        exact (mul_ne_zero (mul_ne_zero hσne (ne_of_gt (hpos ()).1)) hvne) hzaxis
      · apply havoidP k t ht
        rw [hPeq]
        apply Or.inl ∘ Or.inr
        refine ⟨⟨hza,?_⟩,hzT⟩
        intro hs
        have hside : g k t ∈ range D.firstSide := image_subset_range _ _ hs
        have he : g k t=D.firstSide 0 := mem_singleton_iff.mp
          ((hg k).2.2.2 ▸ (show g k t ∈ range (g k) ∩ range D.firstSide from ⟨mem_range_self t,hside⟩))
        have ht0 : t=0 := (hg k).1.injective (he.trans (hg k).2.1.symm)
        have hh := congrArg Subtype.val ht0
        change (t:ℝ)=0 at hh
        exact ht.ne' hh
    have htargetB (k : Bool) : g k 1 ∈ b.val.image := by
      obtain ⟨v,hv,hgv⟩ := hcoords' k 1
      have hfr := hframe () 1 v (by simpa only [sub_self,abs_zero] using (hpos ()).2)
      apply ((hF ()).2.2.2.2 _ (hgv.symm ▸ hfr.1)).mpr
      rw [hgv,hfr.2,D.first_one]
      have hp0 : F () D.secondCorner=0 := D.first_one ▸ (hF ()).2.2.1
      rw [hp0]
      rfl
    have hmeetB (k : Bool) (t : Interval) (ht : 0 < (t:ℝ))
        (hzB : g k t ∈ b.val.image) : t=1 := by
      obtain ⟨v,hv,hgv⟩ := hcoords' k t
      have hzT : g k t ∈ T := by
        by_contra hn
        apply havoidP k t ht
        rw [hPeq]
        exact Or.inr ⟨hzB,hn⟩
      have hnear := hTframe t v (hgv ▸ hzT)
      have hfr := hframe () t v hnear
      have hzero := ((hF ()).2.2.2.2 _ (hTF hzT)).mp hzB
      rw [hgv,hfr.2] at hzero
      change F () (D.firstSide t) 0=0 at hzero
      have hfr0 := hframe () t ⟨0,by norm_num⟩ hnear
      have hsideF : D.firstSide t ∈ (F ()).source := hcenter t ▸ hfr0.1
      have hone := ((hF ()).2.2.2.1 _ hsideF).mp (D.first_on_curve (mem_range_self t))
      have heF : F () (D.firstSide t)=0 := by
        ext j
        fin_cases j
        · exact hzero
        · exact hone
      have hp0 : F () D.secondCorner=0 := D.first_one ▸ (hF ()).2.2.1
      have hpF : D.secondCorner ∈ (F ()).source := D.first_one ▸ (hF ()).2.1
      have he : D.firstSide t=D.secondCorner :=
        (F ()).injOn hsideF hpF (heF.trans hp0.symm)
      exact D.first_embedded.injective (he.trans D.first_one.symm)
    let w : Bool → Interval → Icc (-1:ℝ) 1 := fun k t =>
      ⟨(if k then (1:ℝ) else -1)*h 1*(t:ℝ),by
        have hb : |(if k then (1:ℝ) else -1)*h 1*(t:ℝ)| ≤ 1 := by
          rw [abs_mul,abs_mul,abs_of_nonneg (hbound 1).1,abs_of_nonneg t.property.1]
          have hs : |(if k then (1:ℝ) else -1)|=1 := by cases k <;> norm_num
          rw [hs,one_mul]
          exact (mul_le_of_le_one_right (hbound 1).1 t.property.2).trans
            ((hbound 1).2.trans (hρhalf.trans (by norm_num)))
        exact abs_le.mp hb⟩
    have hw (k : Bool) : Continuous (w k) := by dsimp [w]; fun_prop
    let n : Bool → C(Interval,S) := fun k =>
      ⟨fun t => R (1,w k t),hR.continuous.comp (continuous_const.prodMk (hw k))⟩
    have hn0 (k : Bool) : n k 0=D.secondCorner := by
      change R (1,w k 0)=_
      have hw0 : w k 0=⟨0,by norm_num⟩ := by apply Subtype.ext; simp [w]
      rw [hw0,hcenter,D.first_one]
    have hn1 (k : Bool) : n k 1=g k 1 := by
      obtain ⟨v,hv,hgv⟩ := hcoords' k 1
      have hw1 : w k 1=v := by apply Subtype.ext; simpa [w] using hv.symm
      change R (1,w k 1)=_
      rw [hw1,hgv]
    have hnEmb (k : Bool) : IsEmbedding (n k) := by
      apply (n k).continuous.isClosedEmbedding _ |>.isEmbedding
      intro t u he
      have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hR.injective he)
      change (if k then (1:ℝ) else -1)*h 1*(t:ℝ)=
        (if k then (1:ℝ) else -1)*h 1*(u:ℝ) at hh
      apply Subtype.ext
      have hp := hpositive 1 (by norm_num)
      have hsne : (if k then (1:ℝ) else -1) ≠ 0 := by cases k <;> norm_num
      exact mul_left_cancel₀ (mul_ne_zero hsne (ne_of_gt hp)) hh
    have hnB (k : Bool) : range (n k) ⊆ b.val.image := by
      rintro z ⟨t,rfl⟩
      have hf := hframe () 1 (w k t) (by simpa only [sub_self,abs_zero] using (hpos ()).2)
      apply ((hF ()).2.2.2.2 _ hf.1).mpr
      change F () (R (1,w k t)) 0=0
      rw [hf.2,D.first_one]
      have hp0 : F () D.secondCorner=0 := D.first_one ▸ (hF ()).2.2.1
      rw [hp0]
      rfl
    have hnQ (k : Bool) : Disjoint (range (n k))
        ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) := by
      apply disjoint_left.mpr
      rintro z ⟨t,rfl⟩ hzQ
      have hf := hframe () 1 (w k t) (by simpa only [sub_self,abs_zero] using (hpos ()).2)
      exact disjoint_left.mp (hF ()).1 hf.1 hzQ
    have hnInter : range (n false) ∩ range (n true)={D.secondCorner} := by
      ext z
      constructor
      · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
        have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ))
          (hR.injective (ht.trans hu.symm))
        change -1*h 1*(t:ℝ)=1*h 1*(u:ℝ) at hh
        have hp := hpositive 1 (by norm_num)
        have ht0 : t=0 := Subtype.ext (by
          change (t:ℝ)=0
          have htmul : h 1*(t:ℝ)=0 := by
            nlinarith [mul_nonneg hp.le t.property.1,mul_nonneg hp.le u.property.1]
          exact (mul_eq_zero.mp htmul).resolve_left (ne_of_gt hp))
        exact mem_singleton_iff.mpr (ht.symm.trans (ht0 ▸ hn0 false))
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,hn0 false⟩,⟨0,hn0 true⟩⟩
    have hHom (k : Bool) :
        ∃ (hp : D.firstCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hq : D.secondCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hz : g k 1 ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ),
        ∃ (rail : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g k 1,hz⟩)
          (side : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨D.secondCorner,hq⟩)
          (normal : Path (⟨D.secondCorner,hq⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g k 1,hz⟩),
          (∀ t,(rail t:S)=g k t) ∧ (∀ t,(side t:S)=D.secondSide t) ∧
          (∀ t,(normal t:S)=n k t) ∧ rail.Homotopic (side.trans normal) := by
      let X : Set S := ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ
      have hmarksP : (M.cover.branch:Set S) ⊆ P := by
        intro z hz
        rw [hPeq]
        exact Or.inl (Or.inl (Or.inl hz))
      have hband' (t : Interval) (v : Icc (-1:ℝ) 1) (ht : 0 < (t:ℝ))
          (hv : |(v:ℝ)| ≤ h t) : R (t,v) ∉ P := by
        simpa only [one_mul] using hband t v ht hv
      have hMap := actual_embedded_side_band_into_actual_puncture_private
        D.firstSide 1 (by norm_num) (by norm_num) R hR hcenter ρ hρ hρhalf h hh0
        (hflat 1 (by norm_num)) hbound P hmarksP hband k
      obtain ⟨H,hHbottom,hHleft,hHcoords⟩ :
          ∃ H : C(Interval × Interval,X),
            (∀ t,(H (t,0):S)=D.firstSide t) ∧
            (∀ z : Interval,(H (0,z):S)=D.firstCorner) ∧
            ∀ t z : Interval,∃ v : Icc (-1:ℝ) 1,
              (v:ℝ)=(if k then (1:ℝ) else -1)*h t*(z:ℝ) ∧ (H (t,z):S)=R (t,v) := by
        rw [D.first_zero] at hMap
        simpa only [X,one_mul,Subtype.coe_eta] using hMap
      have hHtop (t : Interval) : (H (t,1):S)=g k t := by
        obtain ⟨v,hv,hHv⟩ := hHcoords t 1
        obtain ⟨v',hv',hgV⟩ := hcoords' k t
        have hv1 : (v:ℝ)=(if k then (1:ℝ) else -1)*h t := by
          change (v:ℝ)=(if k then (1:ℝ) else -1)*h t*1 at hv
          simpa only [mul_one] using hv
        have he : v=v' := Subtype.ext (hv1.trans hv'.symm)
        rw [hHv,he,←hgV]
      have hHright (t : Interval) : (H (1,t):S)=n k t := by
        obtain ⟨v,hv,hHv⟩ := hHcoords 1 t
        have he : v=w k t := Subtype.ext hv
        rw [hHv,he]
        rfl
      have hp : D.firstCorner ∈ X := by simp [X]
      have hq : D.secondCorner ∈ X := by intro hm; exact h1 hm.1
      have hz : g k 1 ∈ X := hHtop 1 ▸ (H (1,1)).property
      let bp : X := ⟨D.firstCorner,hp⟩
      have hleft : ∀ t,H (0,t)=bp := fun t => Subtype.ext (hHleft t)
      obtain ⟨rail,bottom,normal,hrail,hbottom,hnormal,hh⟩ :=
        actual_based_square_boundary_path_homotopy_private H bp hleft
      have hqEnd : (⟨D.secondCorner,hq⟩:X)=H (1,0) :=
        Subtype.ext ((hHbottom 1).trans D.first_one).symm
      have hzEnd : (⟨g k 1,hz⟩:X)=H (1,1) := Subtype.ext (hHtop 1).symm
      let rail' := rail.cast rfl hzEnd
      let bottom' := bottom.cast rfl hqEnd
      let normal' := normal.cast hqEnd hzEnd
      have htransEq : (bottom.trans normal).cast rfl hzEnd=bottom'.trans normal' :=
        Path.cast_trans bottom normal rfl hqEnd hzEnd
      have hh' : rail'.Homotopic (bottom'.trans normal') := by
        have hm := hh.pathCast rfl hzEnd
        rw [htransEq] at hm
        exact hm
      obtain ⟨hpD,hqD,first,second,hfirst,hsecond,hdHom⟩ :=
        actual_original_half_disk_sides_punctured_homotopy_private D h1
      have hbottomEq : bottom'=first := by
        apply Path.ext
        funext t
        apply Subtype.ext
        exact ((congrArg Subtype.val (hbottom t)).trans (hHbottom t)).trans (hfirst t).symm
      rw [hbottomEq] at hh'
      refine ⟨hp,hq,hz,rail',second,normal',?_,hsecond,?_,
        hh'.trans (hdHom.hcomp (Path.Homotopic.refl normal'))⟩
      · intro t
        exact (congrArg Subtype.val (hrail t)).trans (hHtop t)
      · intro t
        exact (congrArg Subtype.val (hnormal t)).trans (hHright t)
    refine ⟨g,n,hnInter,?_⟩
    intro k
    have hQsub : ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ⊆ P := by
      rw [hPeq]
      exact fun z hz => Or.inl (Or.inl hz)
    refine ⟨(hg k).1,hg0 k,?_,?_,?_,?_,hnEmb k,hn0 k,hn1 k,hnB k,hnQ k,hHom k⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,hz⟩
        by_cases ht : t=0
        · exact mem_singleton_iff.mpr (ht ▸ hg0 k)
        · exact False.elim (hclearA k t (hrealpos t ht) hz)
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,hg0 k⟩,D.first_zero ▸ D.first_on_curve (mem_range_self 0)⟩
    · ext z
      constructor
      · rintro ⟨⟨t,rfl⟩,hz⟩
        by_cases ht : t=0
        · exact mem_insert_iff.mpr (Or.inl (ht ▸ hg0 k))
        · exact mem_insert_of_mem _ (mem_singleton_iff.mpr
            (congrArg (g k) (hmeetB k t (hrealpos t ht) hz)))
      · intro hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          exact ⟨⟨0,hg0 k⟩,D.second_zero ▸ D.second_on_curve (mem_range_self 0)⟩
        · have heq := mem_singleton_iff.mp he
          subst z
          exact ⟨mem_range_self 1,htargetB k⟩
    · ext z
      constructor
      · intro hz
        have hzP : z ∈ range (g k) ∩ P := ⟨hz.1,hQsub hz.2⟩
        have hzbase : z ∈ ({D.firstSide 0}:Set S) := (hg k).2.2.1 ▸ hzP
        simpa only [D.first_zero] using hzbase
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,hg0 k⟩,Or.inl hbase⟩
    · intro hm
      exact havoidP k 1 (by norm_num) (hQsub (Or.inl hm))
  have actual_original_marked_half_disk_rounded_side_with_opposite_terminal_normal_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ g n : C(Interval,S),IsEmbedding g ∧ g 0=D.firstCorner ∧
        range g ∩ (r0 ⟨u.val,hTF u.property⟩).val.image={D.firstCorner} ∧
        range g ∩ (rT u).val.image={D.firstCorner,g 1} ∧
        range g ∩ ((M.cover.branch : Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        g 1 ∉ M.cover.branch ∧ IsEmbedding n ∧ n 0=D.secondCorner ∧ n 1=g 1 ∧
        range n ⊆ (rT u).val.image ∧
        Disjoint (range n) ((M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        range n ∩ range D.secondSide={D.secondCorner} ∧
        ∃ (hp : D.firstCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hq : D.secondCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hz : g 1 ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ),
        ∃ (rail : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g 1,hz⟩)
          (side : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨D.secondCorner,hq⟩)
          (normal : Path (⟨D.secondCorner,hq⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g 1,hz⟩),
          (∀ t,(rail t:S)=g t) ∧ (∀ t,(side t:S)=D.secondSide t) ∧
          (∀ t,(normal t:S)=n t) ∧ rail.Homotopic (side.trans normal) := by
    obtain ⟨g,n,hinter,hg⟩ :=
      actual_original_marked_half_disk_two_rounded_whole_trace_clear_sides_private
        D hbase h1 hempty hcross
    choose hgEmb hg0 hgA hgB hgQ hgfree hnEmb hn0 hn1 hnB hnQ hgHom using hg
    have hnorm (k : Bool) : range (n k) ⊆ range D.secondSide ∨
        range (n k) ∩ range D.secondSide={D.secondCorner} := by
      have hh := actual_essential_terminal_rail_old_side_dichotomy_private (rT u)
        D.secondSide (n k) D.second_embedded (hnEmb k) D.second_on_curve (hnB k)
        (D.second_zero.symm ▸ hbase) ((hn0 k).trans D.second_one.symm)
        (fun t hm => disjoint_left.mp (hnQ k) (mem_range_self t) (Or.inl hm))
      simpa only [D.second_one] using hh
    have hnotBoth : ¬ (range (n false) ⊆ range D.secondSide ∧
        range (n true) ⊆ range D.secondSide) :=
      actual_two_terminal_rails_not_both_inside_embedded_old_side_private
        D.secondSide D.second_embedded n hnEmb (fun k => (hn0 k).trans D.second_one.symm)
        (by simpa only [D.second_one] using hinter)
    obtain ⟨k,hk⟩ : ∃ k,range (n k) ∩ range D.secondSide={D.secondCorner} := by
      rcases hnorm false with hf | hf
      · rcases hnorm true with ht | ht
        · exact False.elim (hnotBoth ⟨hf,ht⟩)
        · exact ⟨true,ht⟩
      · exact ⟨false,hf⟩
    exact ⟨g k,n k,hgEmb k,hg0 k,hgA k,hgB k,hgQ k,hgfree k,
      hnEmb k,hn0 k,hn1 k,hnB k,hnQ k,hk,hgHom k⟩
  have actual_original_marked_half_disk_embedded_old_core_and_retained_pieces_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (c g : C(Interval,S)) (R : Set S),
        IsEmbedding c ∧ IsEmbedding g ∧ c 0=D.firstCorner ∧ g 0=D.firstCorner ∧ c 1=g 1 ∧
        range c ⊆ (rT u).val.image ∧ D.secondCorner ∈ range c ∧
        range c ∩ range g={D.firstCorner,g 1} ∧
        range g ∩ (r0 ⟨u.val,hTF u.property⟩).val.image={D.firstCorner} ∧
        range g ∩ (rT u).val.image={D.firstCorner,g 1} ∧
        range g ∩ ((M.cover.branch:Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        range c ∩ ((M.cover.branch:Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        IsCompact R ∧ (rT u).val.image=range c ∪ R ∧
        range c ∩ R={D.firstCorner,g 1} ∧
        Disjoint (R ∩ arcInterior M (r0 ⟨u.val,hTF u.property⟩)) (range c) ∧
        g 1 ∉ M.cover.branch ∧
        ∃ (hp : D.firstCorner ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)
          (hz : g 1 ∈ ((M.cover.branch:Set S) \ {D.firstCorner})ᶜ),
        ∃ core rail : Path (⟨D.firstCorner,hp⟩:↥(((M.cover.branch:Set S) \ {D.firstCorner})ᶜ)) ⟨g 1,hz⟩,
          (∀ t,(core t:S)=c t) ∧ (∀ t,(rail t:S)=g t) ∧ core.Homotopic rail := by
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨g,n,hg,hg0,hgA,hgB,hgQ,hgfree,hn,hn0,hn1,hnB,hnQ,hnD,hHom⟩ :=
      actual_original_marked_half_disk_rounded_side_with_opposite_terminal_normal_private
        D hbase h1 hempty hcross
    let p : Path D.firstCorner D.secondCorner := ⟨D.secondSide,D.second_zero,D.second_one⟩
    let q : Path D.secondCorner (g 1) := ⟨n,hn0,hn1⟩
    let c : C(Interval,S) := (p.trans q).toContinuousMap
    have hc : IsEmbedding c := CurveComplex.LocalSurgery.actualEmbeddedContactPathTrans
      p q D.second_embedded hn (by change range D.secondSide ∩ range n={D.secondCorner}; rw [Set.inter_comm]; exact hnD)
    have hcr : range c=range D.secondSide ∪ range n := Path.trans_range p q
    have hc0 : c 0=D.firstCorner := (p.trans q).source
    have hc1 : c 1=g 1 := (p.trans q).target
    have hcb : range c ⊆ b.val.image := by rw [hcr]; exact union_subset D.second_on_curve hnB
    have hpC : D.secondCorner ∈ range c := by rw [hcr]; exact Or.inl ⟨1,D.second_one⟩
    have hcg : range c ∩ range g={D.firstCorner,g 1} := by
      ext z
      constructor
      · intro hz
        exact hgB ▸ (show z ∈ range g ∩ b.val.image from ⟨hz.2,hcb hz.1⟩)
      · intro hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          exact ⟨⟨0,hc0⟩,⟨0,hg0⟩⟩
        · have heq := mem_singleton_iff.mp he
          subst z
          exact ⟨⟨1,hc1⟩,mem_range_self 1⟩
    let Q : Set S := (M.cover.branch:Set S) ∪ actualObjectTrace M r J
    have hcQ : range c ∩ Q={D.firstCorner} := by
      ext z
      constructor
      · rintro ⟨hzC,hzQ⟩
        rw [hcr] at hzC
        rcases hzC with hzD | hzN
        · have hm := actual_original_pair_closed_obstacle_contact_is_marked
            ⟨Or.inr (D.second_on_curve hzD),hzQ⟩
          have hzDisk : z ∈ range D.disk := image_subset_range _ _
            (D.boundary_eq.symm ▸ (show z ∈ range D.firstSide ∪ range D.secondSide from Or.inr hzD))
          rcases mem_insert_iff.mp (D.marks_are_corners z hzDisk hm) with he | he
          · exact mem_singleton_iff.mpr he
          · exact False.elim (h1 ((mem_singleton_iff.mp he) ▸ hm))
        · exact False.elim (disjoint_left.mp hnQ hzN hzQ)
      · intro hz
        have he := mem_singleton_iff.mp hz
        subst z
        exact ⟨⟨0,hc0⟩,Or.inl hbase⟩
    let R : Set S := b.val.image \ (c '' Ioo (0:Interval) 1)
    have hR : IsCompact R := actual_essential_subarc_outside_open_side_is_compact b c hc hcb
    have hwhole : b.val.image=range c ∪ R := by
      ext z
      constructor
      · intro hz
        by_cases hin : z ∈ c '' Ioo (0:Interval) 1
        · exact Or.inl (image_subset_range _ _ hin)
        · exact Or.inr ⟨hz,hin⟩
      · intro hz
        exact hz.elim (fun hz => hcb hz) (fun hz => hz.1)
    have hCR : range c ∩ R={D.firstCorner,g 1} := by
      ext z
      constructor
      · rintro ⟨⟨t,ht⟩,hzR⟩
        by_cases ht0 : t=0
        · exact mem_insert_iff.mpr (Or.inl (ht.symm.trans ((congrArg c ht0).trans hc0)))
        by_cases ht1 : t=1
        · exact mem_insert_of_mem _ (mem_singleton_iff.mpr (ht.symm.trans ((congrArg c ht1).trans hc1)))
        have htI : t ∈ Ioo (0:Interval) 1 :=
          ⟨lt_of_le_of_ne (show (0:Interval) ≤ t from t.property.1) (Ne.symm ht0),
            lt_of_le_of_ne (show t ≤ (1:Interval) from t.property.2) ht1⟩
        exact False.elim (hzR.2 ⟨t,htI,ht⟩)
      · intro hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z
          refine ⟨⟨0,hc0⟩,hcb ⟨0,hc0⟩,?_⟩
          rintro ⟨t,ht,he⟩
          exact ht.1.ne' (hc.injective (he.trans hc0.symm))
        · have heq := mem_singleton_iff.mp he
          subst z
          refine ⟨⟨1,hc1⟩,hcb ⟨1,hc1⟩,?_⟩
          rintro ⟨t,ht,he⟩
          exact ht.2.ne (hc.injective (he.trans hc1.symm))
    have hportNotA : g 1 ∉ a.val.image := by
      intro hz
      have he : g 1=D.firstCorner := mem_singleton_iff.mp
        (hgA ▸ (show g 1 ∈ range g ∩ a.val.image from ⟨mem_range_self 1,hz⟩))
      exact one_ne_zero (hg.injective (he.trans hg0.symm))
    have hretain : Disjoint (R ∩ arcInterior M a) (range c) := by
      apply disjoint_left.mpr
      intro z hz hzC
      have hh : z ∈ ({D.firstCorner,g 1}:Set S) := hCR ▸ ⟨hzC,hz.1⟩
      rcases mem_insert_iff.mp hh with he | he
      · exact hz.2.2 (he.symm ▸ hbase)
      · exact hportNotA ((mem_singleton_iff.mp he) ▸ hz.2.1)
    obtain ⟨hp,hq,hz,rail,side,normal,hrail,hside,hnormal,hh⟩ := hHom
    let core := side.trans normal
    have hcore (t : Interval) : (core t:S)=c t := by
      change ((side.trans normal) t:S)=(p.trans q) t
      simp only [Path.trans_apply]
      split_ifs
      · exact hside _
      · exact hnormal _
    exact ⟨c,g,R,hc,hg,hc0,hg0,hc1,hcb,hpC,hcg,hgA,hgB,hgQ,hcQ,hR,hwhole,hCR,hretain,hgfree,
      hp,hz,core,rail,hcore,hrail,hh.symm⟩
  have actual_punctured_embedded_core_rounded_side_support_disk_private
      (f g : C(Interval,S)) (u₀ v₀ : S)
      (hf : IsEmbedding f) (hg : IsEmbedding g)
      (hf0 : f 0=u₀) (hg0 : g 0=u₀) (hf1 : f 1=v₀) (hg1 : g 1=v₀)
      (hne : u₀≠v₀) (hinter : range f ∩ range g={u₀,v₀})
      (hu₀ : u₀ ∈ ((M.cover.branch:Set S) \ {u₀})ᶜ)
      (hv₀ : v₀ ∈ ((M.cover.branch:Set S) \ {u₀})ᶜ)
      (α β : Path (⟨u₀,hu₀⟩:↥(((M.cover.branch:Set S) \ {u₀})ᶜ)) ⟨v₀,hv₀⟩)
      (hα : ∀ t,(α t:S)=f t) (hβ : ∀ t,(β t:S)=g t)
      (hhom : α.Homotopic β) :
      ∃ d : C(Metric.closedBall (0:Plane) 1,S), IsEmbedding d ∧
        d '' {x | x.val ∈ Metric.sphere (0:Plane) 1}=range f ∪ range g ∧
        (∀ z ∈ range d,z ∈ M.cover.branch → z=u₀) ∧
        Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (M.cover.branch:Set S) := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨Ω,hn,hconn,hsub,hmax,hfrontier,hfree⟩ :=
      actual_punctured_homotopic_jordan_sides_have_empty_region
        M f g u₀ v₀ hf hg hf0 hg0 hf1 hg1 hne hinter
        hu₀ hv₀ α β hα hβ hhom
    have hboundaryMarks : ∀ z ∈ range f ∪ range g,
        z ∈ M.cover.branch → z=u₀ := by
      intro z hz hzm
      rcases hz with ⟨t,rfl⟩ | ⟨t,rfl⟩
      · have ht := (α t).property
        rw [hα] at ht
        by_contra he
        exact ht ⟨hzm,by simpa using he⟩
      · have ht := (β t).property
        rw [hβ] at ht
        by_contra he
        exact ht ⟨hzm,by simpa using he⟩
    have hcollision : ∀ s t : Interval,f s=g t →
        (s=0 ∧ t=0) ∨ (s=1 ∧ t=1) := by
      intro s t he
      have hx : f s ∈ ({u₀,v₀} : Set S) := by
        rw [←hinter]; exact ⟨mem_range_self s,⟨t,he.symm⟩⟩
      rcases hx with hx | hx
      · exact Or.inl ⟨hf.injective (hx.trans hf0.symm),
          hg.injective (he.symm.trans (hx.trans hg0.symm))⟩
      · rw [mem_singleton_iff] at hx
        exact Or.inr ⟨hf.injective (hx.trans hf1.symm),
          hg.injective (he.symm.trans (hx.trans hg1.symm))⟩
    obtain ⟨c,hc⟩ := CurveComplex.exists_curve_of_two_arcs f g hf.injective hg.injective
      (hf0.trans hg0.symm) (hf1.trans hg1.symm) hcollision
    obtain ⟨Jc,hJc⟩ := actualCurve_sphereJordan M c
    let Lc : C(Interval,S) :=
      ⟨M.sphere.symm ∘ Jc.map,M.sphere.symm.continuous.comp Jc.continuous⟩
    have hLc : range Lc=range f ∪ range g := by
      change range (M.sphere.symm ∘ Jc.map)=_
      rw [range_comp]
      change M.sphere.symm '' Jc.image=_
      rw [hJc,hc,←image_comp,M.sphere.symm_comp_self,image_id]
    have hcard : ({u₀} : Finset S).card<M.cover.branch.card := by
      rw [M.cover.branch_card]; simp
    obtain ⟨q,hqm,hqnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hq : q ∉ range Lc := by
      intro hq
      have he := hboundaryMarks q (hLc ▸ hq) hqm
      exact hqnot (by simp [he])
    have hΩ : IsComplementComponent (range Lc) Ω :=
      hLc.symm ▸ ⟨hn,hconn,hsub,hmax⟩
    obtain ⟨d,hd,hi,hbdy⟩ := actual_selected_jordan_component_embedded_disk M Lc
      (congrArg M.sphere.symm Jc.closed)
      (fun s t he => Jc.injective_except_ends s t (M.sphere.symm.injective he))
      q hq Ω hΩ (hLc.symm ▸ hfrontier)
    have hdfree : Disjoint (d '' {x | x.val ∈ Metric.ball
        (0 : EuclideanSpace ℝ (Fin 2)) 1}) (M.cover.branch : Set S) :=
      hi.symm ▸ hfree
    have hdboundary : d '' {x | x.val ∈ Metric.sphere
        (0 : EuclideanSpace ℝ (Fin 2)) 1}=range f ∪ range g := hbdy.trans hLc
    have hdcorner : ∀ z ∈ range d,z ∈ M.cover.branch → z=u₀ := by
      rintro z ⟨x,rfl⟩ hzm
      have hxnorm : ‖x.val‖≤1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
      rcases hxnorm.lt_or_eq with hx | hx
      · exact False.elim (disjoint_left.mp hdfree
          ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hx,rfl⟩ hzm)
      · apply hboundaryMarks _ _ hzm
        rw [←hdboundary]
        exact ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hx,rfl⟩
    exact ⟨d,hd,hdboundary,hdcorner,hdfree⟩
  have actual_original_marked_half_disk_actual_core_support_disk_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (c g : C(Interval,S)) (R : Set S)
        (d : C(Metric.closedBall (0:Plane) 1,S)),
        IsEmbedding c ∧ IsEmbedding g ∧ IsEmbedding d ∧
        c 0=D.firstCorner ∧ g 0=D.firstCorner ∧ c 1=g 1 ∧
        range c ⊆ (rT u).val.image ∧ D.secondCorner ∈ range c ∧
        range c ∩ range g={D.firstCorner,g 1} ∧
        range g ∩ (r0 ⟨u.val,hTF u.property⟩).val.image={D.firstCorner} ∧
        range g ∩ (rT u).val.image={D.firstCorner,g 1} ∧
        range g ∩ ((M.cover.branch:Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        range c ∩ ((M.cover.branch:Set S) ∪ actualObjectTrace M r J)={D.firstCorner} ∧
        IsCompact R ∧ (rT u).val.image=range c ∪ R ∧
        range c ∩ R={D.firstCorner,g 1} ∧
        Disjoint (R ∩ arcInterior M (r0 ⟨u.val,hTF u.property⟩)) (range c) ∧
        g 1 ∉ M.cover.branch ∧
        d '' {x | x.val ∈ Metric.sphere (0:Plane) 1}=range c ∪ range g ∧
        (∀ z ∈ range d,z ∈ M.cover.branch → z=D.firstCorner) ∧
        Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (M.cover.branch:Set S) ∧
        Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (actualObjectTrace M r J) ∧
        Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) (rT u).val.image := by
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨c,g,R,hc,hg,hc0,hg0,hc1,hcb,hpC,hcg,hgA,hgB,hgQ,hcQ,hR,hwhole,hCR,hretain,hgfree,
      hp,hz,core,rail,hcore,hrail,hhom⟩ :=
      actual_original_marked_half_disk_embedded_old_core_and_retained_pieces_private
        D hbase h1 hempty hcross
    have hne : D.firstCorner≠g 1 := by
      intro he
      have h := hg.injective (hg0.trans he)
      exact zero_ne_one h
    obtain ⟨d,hd,hboundary,hcorner,hmarks⟩ :=
      actual_punctured_embedded_core_rounded_side_support_disk_private c g D.firstCorner (g 1)
        hc hg hc0 hg0 hc1 rfl hne hcg hp hz core rail hcore hrail hhom
    have hboundaryGraph : (range c ∪ range g) ∩ actualObjectTrace M r J ⊆
        (M.cover.branch:Set S) := by
      rintro z ⟨hz,hzG⟩
      have he : z=D.firstCorner := by
        rcases hz with hz | hz
        · exact mem_singleton_iff.mp (hcQ ▸ ⟨hz,Or.inr hzG⟩)
        · exact mem_singleton_iff.mp (hgQ ▸ ⟨hz,Or.inr hzG⟩)
      exact he.symm ▸ hbase
    have hgraph := actual_single_mark_support_disk_boundary_contact_graph_clearance_private
      c g d hd D.firstCorner (g 1) hmarks
      (fun z hz hm => Or.inl (hcorner z hz hm)) (Or.inr hgfree)
      hboundary hboundaryGraph
    have hgB' : range g ∩ (rT u).val.image={g 0,g 1} := by simpa only [hg0] using hgB
    have hexterior := actual_single_mark_support_disk_entire_old_core_carrier_exterior_private
      (rT u) c g hc hcb (hc0.trans hg0.symm) hc1 hgB' d hd hboundary hmarks
    exact ⟨c,g,R,d,hc,hg,hd,hc0,hg0,hc1,hcb,hpC,hcg,hgA,hgB,hgQ,hcQ,
      hR,hwhole,hCR,hretain,hgfree,hboundary,hcorner,hmarks,hgraph,hexterior⟩
  have actual_original_inner_empty_disk_produces_two_actual_terminal_rails
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hDG : Disjoint D.openInterior (actualObjectTrace M r J))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (d : C(Metric.closedBall (0 : Plane) 1,S)) (g rails : Bool → C(Interval,S)),
        IsEmbedding d ∧ range D.disk ⊆ interior (range d) ∧
        Disjoint (range d) ((M.cover.branch:Set S) ∪ actualObjectTrace M r J) ∧
        (∀ s,IsEmbedding (g s) ∧ range (g s) ⊆ interior (range d) ∧
          Disjoint (range (g s)) (r0 ⟨u.val,hTF u.property⟩).val.image ∧
          range (g s) ∩ (rT u).val.image={g s 0,g s 1}) ∧
        (∀ k,IsEmbedding (rails k) ∧ range (rails k) ⊆ interior (range d) ∧
          range (rails k) ⊆ (rT u).val.image ∧
          rails k ⟨1/2,by constructor <;> norm_num⟩=(if k then D.secondCorner else D.firstCorner) ∧
          rails k 0=(if k then g false 1 else g false 0) ∧
          rails k 1=(if k then g true 1 else g true 0)) ∧
        Disjoint (range (rails false)) (range (rails true)) := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨d,hd,hstrict,hdGraph⟩ :=
      actual_original_inner_empty_disk_enlarged_away_from_entire_graph D h0 h1 hDG
    have hdMarks : Disjoint (range d) (M.cover.branch:Set S) := hdGraph.mono_right subset_union_left
    obtain ⟨F,R,hF,hR,hRQ,hcenter,σ,δ,η,hsign,hpos,hcoords'⟩ :=
      actual_original_inner_disk_two_endpoint_crossing_framed_graph_clear_strip D h0 h1 hcross
    let θ : Bool → Interval := fun k => if k then 1 else 0
    have hθ : Function.Injective θ := by
      intro k l he
      cases k <;> cases l <;> simp [θ] at he ⊢
    have hcharts (k : Bool) : (F k).source ⊆
        ((M.cover.branch:Set S) ∪ actualObjectTrace M r J)ᶜ ∧
        Disjoint (F k).source (M.cover.branch:Set S) ∧
        D.firstSide (θ k) ∈ (F k).source ∧ F k (D.firstSide (θ k))=0 ∧
        (∀ x ∈ (F k).source,x ∈ a.val.image ↔ F k x 1=0) ∧
        (∀ x ∈ (F k).source,x ∈ b.val.image ↔ F k x 0=0) := by
      exact ⟨fun z hz hzQ => disjoint_left.mp (hF k).1 hz hzQ,
        (hF k).1.mono_right subset_union_left,(hF k).2⟩
    have hcoords k (t : Interval) (v : Icc (-1:ℝ) 1)
        (ht : |(t:ℝ)-(θ k:ℝ)| < η k) :
        R (t,v) ∈ (F k).source ∧
        F k (R (t,v))=Plane.mk (F k (D.firstSide t) 0) (σ k*δ k*(v:ℝ)) := by
      apply hcoords' k t v
      cases k <;> simpa [θ] using ht
    let q : Interval → Interval := id
    have hq : Continuous q := continuous_id
    have hqi : Function.Injective q := Function.injective_id
    have hq0 : q 0=θ false := rfl
    have hq1 : q 1=θ true := rfl
    have hmap (t : Interval) : D.firstSide (q t)=D.firstSide t := rfl
    have hθcorner (k : Bool) : D.firstSide (θ k)=if k then D.secondCorner else D.firstCorner := by
      cases k
      · exact D.first_zero
      · exact D.first_one
    have hc0 : D.firstSide (θ false)=D.firstCorner := D.first_zero
    have hc1 : D.firstSide (θ true)=D.secondCorner := D.first_one
    have hsmall (k : Bool) : ∃ T : Set S, IsOpen T ∧ D.firstSide (θ k) ∈ T ∧ T ⊆ (F k).source ∧
        ∀ z, R z ∈ T → |(z.1:ℝ)-(θ k:ℝ)| < η k := by
      let Z := Interval × Icc (-1:ℝ) 1
      let K : Set Z := {z | η k ≤ |(z.1:ℝ)-(θ k:ℝ)|}
      have hc : Continuous (fun z : Z => |(z.1:ℝ)-(θ k:ℝ)|) := by
        change Continuous (fun z : Interval × Icc (-1:ℝ) 1 => |(z.1:ℝ)-(θ k:ℝ)|)
        fun_prop
      have hK : IsClosed K := isClosed_le continuous_const hc
      have hpnot : D.firstSide (θ k) ∉ R '' K := by
        rintro ⟨z,hz,he⟩
        have hz0 := hR.injective (he.trans (hcenter (θ k)).symm)
        have hle : η k ≤ 0 := by
          change η k ≤ |(z.1:ℝ)-(θ k:ℝ)| at hz
          rw [hz0] at hz
          simpa using hz
        exact (not_le_of_gt (hpos k).2) hle
      let T : Set S := (F k).source ∩ (R '' K)ᶜ
      refine ⟨T,(F k).open_source.inter (hK.isCompact.image hR.continuous).isClosed.isOpen_compl,
        ⟨(hcharts k).2.2.1,hpnot⟩,inter_subset_left,?_⟩
      intro z hz
      by_contra hnot
      exact hz.2 ⟨z,le_of_not_gt hnot,rfl⟩
    choose T hT hTp hTF hnear using hsmall
    have hclean : range D.firstSide ∩ b.val.image={D.firstCorner,D.secondCorner} :=
      actual_empty_marked_disk_first_side_clean_private a b
        (fun p hp => actual_marked_crossesInDisk_symm M a b p (hcross p hp)) D hempty
    let K : Set S := a.val.image \ (D.firstSide '' Ioo (0:Interval) 1)
    have hKc : IsCompact K := actual_essential_subarc_outside_open_side_is_compact
      a D.firstSide D.first_embedded D.first_on_curve
    let Q : Set S := (M.cover.branch:Set S) ∪ ((b.val.image ∪ K) ∩ (T false ∪ T true)ᶜ)
    have hQ : IsClosed Q := M.cover.branch.isClosed.union
      (((isCompact_range b.val.continuous).isClosed.union hKc.isClosed).inter
        ((hT false).union (hT true)).isClosed_compl)
    have hsideDisk (t : Interval) : D.firstSide t ∈ range D.disk := by
      apply image_subset_range D.disk _
      rw [D.boundary_eq]
      exact Or.inl (mem_range_self t)
    have haxisQ (t : Interval) : D.firstSide t ∉ Q := by
      rintro (hm | ⟨hb | hK,ht⟩)
      · exact disjoint_left.mp hdMarks (interior_subset (hstrict (hsideDisk t))) hm
      · have hc := hclean ▸ (show D.firstSide t ∈ range D.firstSide ∩ b.val.image from ⟨mem_range_self t,hb⟩)
        rcases mem_insert_iff.mp hc with hc | hc
        · exact ht (Or.inl (hc.symm ▸ (hc0 ▸ hTp false)))
        · exact ht (Or.inr ((mem_singleton_iff.mp hc).symm ▸ (hc1 ▸ hTp true)))
      · by_cases ht0 : t=0
        · exact ht (Or.inl (ht0 ▸ (hc0 ▸ hTp false)))
        by_cases ht1 : t=1
        · exact ht (Or.inr (ht1 ▸ (hc1 ▸ hTp true)))
        exact hK.2 ⟨t,⟨lt_of_le_of_ne t.property.1 (Ne.symm ht0),
          lt_of_le_of_ne t.property.2 ht1⟩,rfl⟩
    let U : Set S := interior (range d) ∩ Qᶜ
    have hU : IsOpen U := isOpen_interior.inter hQ.isOpen_compl
    obtain ⟨ρ,hρ,hρhalf,hband⟩ := actual_compact_axis_uniform_band_inside_open R hR.continuous q hq U hU
      (fun t => by rw [hcenter,hmap]; exact ⟨hstrict (hsideDisk t),haxisQ t⟩)
    let v (s : Bool) : Icc (-1:ℝ) 1 := ⟨if s then ρ else -ρ,by cases s <;> constructor <;> dsimp <;> linarith⟩
    have hv (s : Bool) : |(v s:ℝ)|=ρ := by cases s <;> simp [v,abs_of_pos hρ,abs_of_neg (neg_neg_of_pos hρ)]
    have hvne (s : Bool) : (v s:ℝ) ≠ 0 := by intro he; have hh := hv s; rw [he,abs_zero] at hh; linarith
    let g (s : Bool) : C(Interval,S) := ⟨fun t => R (q t,v s),hR.continuous.comp (hq.prodMk continuous_const)⟩
    have hg (s : Bool) : IsEmbedding (g s) := ((g s).continuous.isClosedEmbedding (by
      intro t u he
      exact hqi (congrArg Prod.fst (hR.injective he)))).isEmbedding
    have hgU (s : Bool) (t : Interval) : g s t ∈ U := hband t (v s) (hv s).le
    have hgA (s : Bool) : Disjoint (range (g s)) a.val.image := by
      apply disjoint_left.mpr
      rintro z ⟨t,rfl⟩ ha
      by_cases htT : g s t ∈ T false ∪ T true
      · obtain ⟨k,hkt⟩ : ∃ k : Bool,g s t ∈ T k := by
          rcases htT with ht | ht
          · exact ⟨false,ht⟩
          · exact ⟨true,ht⟩
        have hn := hnear k (q t,v s) hkt
        have hf := hcoords k (q t) (v s) hn
        have hh := ((hcharts k).2.2.2.2.1 _ (hTF k hkt)).mp ha
        change F k (R (q t,v s)) 1=0 at hh
        rw [hf.2] at hh
        change σ k*δ k*(v s:ℝ)=0 at hh
        have hσ : σ k ≠ 0 := by rcases hsign k with h | h <;> rw [h] <;> norm_num
        exact hvne s ((mul_eq_zero.mp hh).resolve_left
          (mul_ne_zero hσ (ne_of_gt (hpos k).1)))
      · have hnotK : g s t ∉ K := fun hK => (hgU s t).2 (Or.inr ⟨Or.inr hK,htT⟩)
        have hin : g s t ∈ D.firstSide '' Ioo (0:Interval) 1 := by
          by_contra hn
          exact hnotK ⟨ha,hn⟩
        obtain ⟨w,hw,he⟩ := hin
        have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => z.2.val)
          (hR.injective (he.symm.trans (hcenter w).symm))
        exact hvne s hh
    have hBaxis (k : Bool) := (hcharts k).2.2.2.2.2
    have hgB0 (s : Bool) : g s 0 ∈ b.val.image := by
      have hnear0 : |(q 0:ℝ)-(θ false:ℝ)| < η false := by rw [hq0]; simpa using (hpos false).2
      have hf := hcoords false (q 0) (v s) hnear0
      apply (hBaxis false (g s 0) hf.1).mpr
      change F false (R (q 0,v s)) 0=0
      rw [hf.2,hq0]
      have hzero := (hcharts false).2.2.2.1
      change F false (D.firstSide (θ false)) 0=0
      exact congrArg (fun z : Plane => z 0) hzero
    have hgB1 (s : Bool) : g s 1 ∈ b.val.image := by
      have hnear1 : |(q 1:ℝ)-(θ true:ℝ)| < η true := by rw [hq1]; simpa using (hpos true).2
      have hf := hcoords true (q 1) (v s) hnear1
      apply (hBaxis true (g s 1) hf.1).mpr
      change F true (R (q 1,v s)) 0=0
      rw [hf.2,hq1]
      have hzero := (hcharts true).2.2.2.1
      change F true (D.firstSide (θ true)) 0=0
      exact congrArg (fun z : Plane => z 0) hzero
    have hgmeet (s : Bool) : range (g s) ∩ b.val.image={g s 0,g s 1} := by
      apply Subset.antisymm
      · rintro z ⟨⟨t,rfl⟩,hbt⟩
        have htT : g s t ∈ T false ∪ T true := by
          by_contra ht
          exact (hgU s t).2 (Or.inr ⟨Or.inl hbt,ht⟩)
        obtain ⟨k,hkt⟩ : ∃ k : Bool, g s t ∈ T k := by
          rcases htT with ht | ht
          · exact ⟨false,ht⟩
          · exact ⟨true,ht⟩
        have hn := hnear k (q t,v s) hkt
        have hf := hcoords k (q t) (v s) hn
        have hcz := hcoords k (q t) ⟨0,by norm_num⟩ hn
        have hbcenter : D.firstSide t ∈ b.val.image := by
          apply (hBaxis k _ ((hcenter _).symm ▸ hcz.1)).mpr
          have hh := (hBaxis k _ (hTF k hkt)).mp hbt
          change F k (R (q t,v s)) 0=0 at hh
          rw [hf.2] at hh
          exact hh
        have hc := hclean ▸ (show D.firstSide t ∈ range D.firstSide ∩ b.val.image from ⟨mem_range_self t,(hmap t) ▸ hbcenter⟩)
        rcases mem_insert_iff.mp hc with hc | hc
        · have ht : t=0 := D.first_embedded.injective (hc.trans D.first_zero.symm)
          exact mem_insert_iff.mpr (Or.inl (congrArg (g s) ht))
        · have ht : t=1 := D.first_embedded.injective ((mem_singleton_iff.mp hc).trans D.first_one.symm)
          exact mem_insert_of_mem _ (mem_singleton_iff.mpr (congrArg (g s) ht))
      · intro z hz
        rcases mem_insert_iff.mp hz with he | he
        · subst z; exact ⟨mem_range_self _,hgB0 s⟩
        · subst z; exact ⟨mem_range_self _,hgB1 s⟩
    let w : Interval → Icc (-1:ℝ) 1 := fun t => ⟨ρ*(2*(t:ℝ)-1),by constructor <;> nlinarith [t.property.1,t.property.2]⟩
    have hw (t : Interval) : |(w t:ℝ)| ≤ ρ := by rw [abs_le]; dsimp [w]; constructor <;> nlinarith [t.property.1,t.property.2]
    let r (k : Bool) : C(Interval,S) := ⟨fun t => R (θ k,w t),hR.continuous.comp (by dsimp [w]; fun_prop)⟩
    have hr (k : Bool) : IsEmbedding (r k) := ((r k).continuous.isClosedEmbedding (by
      intro t u he
      have hh := congrArg (fun z : Interval × Icc (-1:ℝ) 1 => (z.2:ℝ)) (hR.injective he)
      apply Subtype.ext
      dsimp [w] at hh
      nlinarith)).isEmbedding
    have hrU (k : Bool) (t : Interval) : r k t ∈ U := by
      cases k
      · change R (θ false,w t) ∈ U
        rw [← hq0]
        exact hband 0 (w t) (hw t)
      · change R (θ true,w t) ∈ U
        rw [← hq1]
        exact hband 1 (w t) (hw t)
    have hrB (k : Bool) (t : Interval) : r k t ∈ b.val.image := by
      have hn : |(θ k:ℝ)-(θ k:ℝ)| < η k := by simpa using (hpos k).2
      have hf := hcoords k (θ k) (w t) hn
      apply (hBaxis k (r k t) hf.1).mpr
      change F k (R (θ k,w t)) 0=0
      rw [hf.2,(hcharts k).2.2.2.1]
      rfl
    refine ⟨d,g,r,hd,hstrict,hdGraph,?_,?_,?_⟩
    · intro s
      exact ⟨hg s,by rintro z ⟨t,rfl⟩; exact (hgU s t).1,hgA s,hgmeet s⟩
    · intro k
      refine ⟨hr k,by rintro z ⟨t,rfl⟩; exact (hrU k t).1,
        by rintro z ⟨t,rfl⟩; exact hrB k t,?_,?_,?_⟩
      · change R (θ k,w _)=_
        have hh : w ⟨1/2,by constructor <;> norm_num⟩ = ⟨0,by norm_num⟩ := by apply Subtype.ext; dsimp [w]; ring
        rw [hh,hcenter,hθcorner]
      · cases k <;> change R (_,w 0)=R (_,v false) <;> simp only [hq0,hq1] <;>
          congr 1 <;> apply Prod.ext <;> try rfl
        all_goals apply Subtype.ext; dsimp [w,v]; ring
      · cases k <;> change R (_,w 1)=R (_,v true) <;> simp only [hq0,hq1] <;>
          congr 1 <;> apply Prod.ext <;> try rfl
        all_goals apply Subtype.ext; dsimp [w,v]; ring
    
    · apply disjoint_left.mpr
      rintro z ⟨t,ht⟩ ⟨u,hu⟩
      have hh := congrArg Prod.fst (hR.injective (ht.trans hu.symm))
      have he : (false : Bool)=true := hθ hh
      exact Bool.false_ne_true he
  have actual_essential_moving_core_between_ports_in_mark_free_connected_trace
      (b : EssentialMarkedArc M) (g : C(Interval,S)) (hg : IsEmbedding g)
      (J : Set S) (hJ : IsConnected J) (hJb : J ⊆ arcInterior M b)
      (h0 : g 0 ∈ J) (h1 : g 1 ∈ J) :
      ∃ (u v : Interval) (c : C(Interval,S)),u ≠ v ∧
        b.val.map u=g 0 ∧ b.val.map v=g 1 ∧ IsEmbedding c ∧
        c 0=g 0 ∧ c 1=g 1 ∧ range c=b.val.map '' uIcc u v ∧ range c ⊆ J := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨e,he⟩ := hActualInteriorParameterHomeomorph M b
    let j : J → arcInterior M b := fun z => ⟨z.val,hJb z.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    let f : J → Interval := fun z => (e.symm (j z)).val
    have hf : Continuous f := continuous_subtype_val.comp (e.symm.continuous.comp hj)
    have hfm (w : J) : b.val.map (f w)=w.val := by
      rw [←he]
      exact congrArg Subtype.val (e.apply_symm_apply (j w))
    have hfi (w : J) : 0 < f w ∧ f w < 1 := by
      have hm : b.val.map (f w) ∉ M.cover.branch := hfm w ▸ (hJb w.property).2
      have hn0 : f w ≠ 0 := fun he => hm (he.symm ▸ b.val.start_marked)
      have hn1 : f w ≠ 1 := fun he => hm (he.symm ▸ b.val.end_marked)
      exact ⟨lt_of_le_of_ne (f w).property.1 (Ne.symm hn0),lt_of_le_of_ne (f w).property.2 hn1⟩
    let u : Interval := f ⟨g 0,h0⟩
    let v : Interval := f ⟨g 1,h1⟩
    have huf : b.val.map u=g 0 := hfm _
    have hvf : b.val.map v=g 1 := hfm _
    have huv : u ≠ v := by intro he; exact zero_ne_one (hg.injective (huf.symm.trans ((congrArg b.val.map he).trans hvf)))
    let q : Interval → Interval := fun t => ⟨(1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ),by
      constructor
      · exact add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) u.property.1) (mul_nonneg t.property.1 v.property.1)
      · nlinarith [u.property.1,u.property.2,v.property.1,v.property.2,t.property.1,t.property.2]⟩
    have hq : Continuous q := by dsimp [q]; fun_prop
    have hq0 : q 0=u := by apply Subtype.ext; dsimp [q]; ring
    have hq1 : q 1=v := by apply Subtype.ext; dsimp [q]; ring
    have hqi : Function.Injective q := by
      intro t s he
      have hh := congrArg Subtype.val he
      have huv' : (u:ℝ) ≠ (v:ℝ) := fun he => huv (Subtype.ext he)
      apply Subtype.ext
      dsimp [q] at hh
      have hz : ((t:ℝ)-(s:ℝ))*((v:ℝ)-(u:ℝ))=0 := by nlinarith only [hh]
      exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr huv'.symm))
    have hqr : range q=uIcc u v := by
      have hfreal : Continuous (fun t : Interval => (q t:ℝ)) := continuous_subtype_val.comp hq
      apply Subset.antisymm
      · rintro z ⟨t,rfl⟩
        rw [mem_uIcc]
        by_cases huvle : u ≤ v
        · left
          have hh : (u:ℝ) ≤ (v:ℝ) := huvle
          constructor
          · change (u:ℝ) ≤ (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ)
            nlinarith [t.property.1,t.property.2]
          · change (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ) ≤ (v:ℝ)
            nlinarith [t.property.1,t.property.2]
        · right
          have hvule : v ≤ u := le_of_not_ge huvle
          have hh : (v:ℝ) ≤ (u:ℝ) := hvule
          constructor
          · change (v:ℝ) ≤ (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ)
            nlinarith [t.property.1,t.property.2]
          · change (1-(t:ℝ))*(u:ℝ)+(t:ℝ)*(v:ℝ) ≤ (u:ℝ)
            nlinarith [t.property.1,t.property.2]
      · intro z hz
        have hzreal : (z:ℝ) ∈ uIcc ((q 0:Interval):ℝ) ((q 1:Interval):ℝ) := by
          rw [hq0,hq1]
          exact hz
        obtain ⟨t,ht,hqt⟩ := intermediate_value_uIcc hfreal.continuousOn hzreal
        exact ⟨t,Subtype.ext hqt⟩
    let c : C(Interval,S) := ⟨b.val.map ∘ q,b.val.continuous.comp hq⟩
    have hc : IsEmbedding c := (c.continuous.isClosedEmbedding (by
      intro t s heq
      apply hqi
      have hqt : q t ∈ uIcc u v := hqr ▸ mem_range_self t
      have hqt01 : 0 < q t ∧ q t < 1 := by
        rw [mem_uIcc] at hqt
        rcases hqt with h | h
        · exact ⟨(hfi ⟨g 0,h0⟩).1.trans_le h.1,h.2.trans_lt (hfi ⟨g 1,h1⟩).2⟩
        · exact ⟨(hfi ⟨g 1,h1⟩).1.trans_le h.1,h.2.trans_lt (hfi ⟨g 0,h0⟩).2⟩
      rcases b.val.injective_except_loop_closure (q t) (q s) heq with h | h | h
      · exact h
      · exact False.elim (ne_of_gt hqt01.1 h.1)
      · exact False.elim (ne_of_lt hqt01.2 h.1))).isEmbedding
    have hcr : range c=b.val.map '' uIcc u v := by rw [← hqr]; exact range_comp b.val.map q
    have hK : _root_.IsPreconnected (range f) := by
      letI : PreconnectedSpace J := Subtype.preconnectedSpace hJ.isPreconnected
      exact isPreconnected_range hf
    have huK : u ∈ range f := ⟨⟨g 0,h0⟩,rfl⟩
    have hvK : v ∈ range f := ⟨⟨g 1,h1⟩,rfl⟩
    have hsub : range c ⊆ J := by
      rw [hcr]
      rintro z ⟨t,ht,rfl⟩
      obtain ⟨w,hw⟩ := hK.ordConnected.uIcc_subset huK hvK ht
      have hm : b.val.map (f w)=w.val := hfm w
      rw [← hw,hm]
      exact w.property
    exact ⟨u,v,c,huv,huf,hvf,hc,by simpa only [c,ContinuousMap.coe_mk,Function.comp_apply,hq0] using huf,
      by simpa only [c,ContinuousMap.coe_mk,Function.comp_apply,hq1] using hvf,hcr,hsub⟩
  have actual_essential_disjoint_terminal_crosssections_select_original_core
      (b : EssentialMarkedArc M) (g r : Bool → C(Interval,S))
      (hr : ∀ k,IsEmbedding (r k))
      (hrb : ∀ k,range (r k) ⊆ arcInterior M b)
      (hdis : Disjoint (range (r false)) (range (r true)))
      (hports0 : ∀ k,r k 0=(if k then g false 1 else g false 0))
      (hports1 : ∀ k,r k 1=(if k then g true 1 else g true 0)) :
      ∃ (s : Bool) (u v : Interval),b.val.map u=g s 0 ∧ b.val.map v=g s 1 ∧
        r false ⟨1/2,by constructor <;> norm_num⟩ ∈ b.val.map '' uIcc u v := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    obtain ⟨e,he⟩ := hActualInteriorParameterHomeomorph M b
    let G (k : Bool) (t : Interval) : Interval :=
      (e.symm ⟨r k t,hrb k (mem_range_self t)⟩).val
    have hG (k : Bool) : Continuous (G k) := continuous_subtype_val.comp
      (e.symm.continuous.comp ((r k).continuous.subtype_mk _))
    have hGm (k : Bool) (t : Interval) : b.val.map (G k t)=r k t := by
      rw [←he]
      exact congrArg Subtype.val (e.apply_symm_apply _)
    have hGi (k : Bool) : Function.Injective (G k) := fun t u he =>
      (hr k).injective ((hGm k t).symm.trans ((congrArg b.val.map he).trans (hGm k u)))
    let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
    let β0 := G false mid
    let β1 := G true mid
    have hnot : β0 ∉ range (G true) := by
      rintro ⟨t,ht⟩
      have he : r false mid=r true t := (hGm false mid).symm.trans ((congrArg b.val.map ht.symm).trans (hGm true t))
      exact disjoint_left.mp hdis (mem_range_self mid) ⟨t,he.symm⟩
    have hne : β0 ≠ β1 := fun he => hnot ⟨mid,he.symm⟩
    have hK : _root_.IsPreconnected (range (G true)) := isPreconnected_range (hG true)
    have hotherUp (hb : β0 < β1) (t : Interval) : β0 < G true t := by
      by_contra hn
      have hle : G true t ≤ β0 := le_of_not_gt hn
      have hm : β0 ∈ uIcc (G true t) β1 := mem_uIcc.mpr (Or.inl ⟨hle,hb.le⟩)
      exact hnot (hK.ordConnected.uIcc_subset (mem_range_self t) (mem_range_self mid) hm)
    have hotherDown (hb : β1 < β0) (t : Interval) : G true t < β0 := by
      by_contra hn
      have hle : β0 ≤ G true t := le_of_not_gt hn
      have hm : β0 ∈ uIcc β1 (G true t) := mem_uIcc.mpr (Or.inl ⟨hb.le,hle⟩)
      exact hnot (hK.ordConnected.uIcc_subset (mem_range_self mid) (mem_range_self t) hm)
    have hm0 : (0:Interval) < mid := by change (0:ℝ)<1/2; norm_num
    have hm1 : mid < (1:Interval) := by change (1/2:ℝ)<1; norm_num
    have hselect : ∃ s : Bool, β0 ∈ uIcc (G false (if s then 1 else 0)) (G true (if s then 1 else 0)) := by
      rcases lt_or_gt_of_ne hne with hb | hb <;>
        rcases (hG false).strictMono_of_inj_boundedOrder' (hGi false) with hg | hg
      · exact ⟨false,mem_uIcc.mpr (Or.inl ⟨(hg hm0).le,(hotherUp hb 0).le⟩)⟩
      · exact ⟨true,mem_uIcc.mpr (Or.inl ⟨(hg hm1).le,(hotherUp hb 1).le⟩)⟩
      · exact ⟨true,mem_uIcc.mpr (Or.inr ⟨(hotherDown hb 1).le,(hg hm1).le⟩)⟩
      · exact ⟨false,mem_uIcc.mpr (Or.inr ⟨(hotherDown hb 0).le,(hg hm0).le⟩)⟩
    obtain ⟨s,hs⟩ := hselect
    refine ⟨s,G false (if s then 1 else 0),G true (if s then 1 else 0),?_,?_,?_⟩
    · cases s
      · exact (hGm false 0).trans (hports0 false)
      · exact (hGm false 1).trans (hports1 false)
    · cases s
      · exact (hGm true 0).trans (hports0 true)
      · exact (hGm true 1).trans (hports1 true)
    · exact ⟨β0,hs,hGm false mid⟩
  have actual_original_inner_disk_produces_graph_clear_supporting_old_core
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hDG : Disjoint D.openInterior (actualObjectTrace M r J))
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ (u₀ v₀ : Interval) (c g : C(Interval,S))
        (e : C(Metric.closedBall (0 : Plane) 1,S)),
        u₀ ≠ v₀ ∧ (rT u).val.map u₀=g 0 ∧ (rT u).val.map v₀=g 1 ∧
        IsEmbedding c ∧ IsEmbedding g ∧ c 0=g 0 ∧ c 1=g 1 ∧
        range c=(rT u).val.map '' uIcc u₀ v₀ ∧ D.firstCorner ∈ range c ∧
        Disjoint (range g) (r0 ⟨u.val,hTF u.property⟩).val.image ∧
        range g ∩ (rT u).val.image={g 0,g 1} ∧ range c ∩ range g={g 0,g 1} ∧
        IsEmbedding e ∧ e '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range c ∪ range g ∧
        Disjoint (range e) ((M.cover.branch:Set S) ∪ actualObjectTrace M r J) := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨d,g,r,hd,hstrict,hdGraph,hg,hr,hdis⟩ :=
      actual_original_inner_empty_disk_produces_two_actual_terminal_rails
        D h0 h1 hempty hDG hcross
    have hbinj (s t : Interval) (he : b.val.map s=b.val.map t)
        (hm : b.val.map s ∉ M.cover.branch) : s=t := by
      rcases b.val.injective_except_loop_closure s t he with h | h | h
      · exact h
      · exact False.elim (hm (h.1.symm ▸ b.val.start_marked))
      · exact False.elim (hm (h.1.symm ▸ b.val.end_marked))
    obtain ⟨s,u,v,hu,hv,hp⟩ := actual_essential_disjoint_terminal_crosssections_select_original_core
      b g r (fun k => (hr k).1) (fun k z hz => ⟨(hr k).2.2.1 hz,fun hm => disjoint_left.mp hdGraph
          (interior_subset ((hr k).2.1 hz)) (Or.inl hm)⟩) hdis
        (fun k => (hr k).2.2.2.2.1) (fun k => (hr k).2.2.2.2.2)
    let mid : Interval := ⟨1/2,by constructor <;> norm_num⟩
    have hr0 : r false mid=D.firstCorner := (hr false).2.2.2.1
    have hr1 : r true mid=D.secondCorner := (hr true).2.2.2.1
    let J : Set S := (range (r false) ∪ range D.secondSide) ∪ range (r true)
    have hJ : IsConnected J :=
      IsConnected.union ⟨D.secondCorner,Or.inr ⟨1,D.second_one⟩,⟨mid,hr1⟩⟩
        (IsConnected.union ⟨D.firstCorner,⟨mid,hr0⟩,⟨0,D.second_zero⟩⟩
          (isConnected_range (r false).continuous) (isConnected_range D.secondSide.continuous))
        (isConnected_range (r true).continuous)
    have hJb : J ⊆ b.val.image := union_subset (union_subset (hr false).2.2.1 D.second_on_curve) (hr true).2.2.1
    have hJN : J ⊆ interior (range d) := by
      apply union_subset (union_subset (hr false).2.1 ?_) (hr true).2.1
      intro z hz
      apply hstrict
      apply image_subset_range D.disk _
      rw [D.boundary_eq]
      exact Or.inr hz
    have hg0 : g s 0 ∈ J := by
      cases s
      · exact Or.inl (Or.inl ⟨0,(hr false).2.2.2.2.1⟩)
      · exact Or.inl (Or.inl ⟨1,(hr false).2.2.2.2.2⟩)
    have hg1 : g s 1 ∈ J := by
      cases s
      · exact Or.inr ⟨0,(hr true).2.2.2.2.1⟩
      · exact Or.inr ⟨1,(hr true).2.2.2.2.2⟩
    obtain ⟨u',v',c,huv,huc,hvc,hc,hc0,hc1,hcr,hcJ⟩ :=
      actual_essential_moving_core_between_ports_in_mark_free_connected_trace b (g s) (hg s).1 J hJ (fun z hz => ⟨hJb hz,fun hm => disjoint_left.mp hdGraph
        (interior_subset (hJN hz)) (Or.inl hm)⟩) hg0 hg1
    have heU : u'=u := hbinj u' u (huc.trans hu.symm) (fun hm =>
      disjoint_left.mp hdGraph (interior_subset ((hg s).2.1 (mem_range_self 0)))
        (Or.inl (huc ▸ hm)))
    have heV : v'=v := hbinj v' v (hvc.trans hv.symm) (fun hm =>
      disjoint_left.mp hdGraph (interior_subset ((hg s).2.1 (mem_range_self 1)))
        (Or.inl (hvc ▸ hm)))
    have hpC : D.firstCorner ∈ range c := by rw [hcr,heU,heV,← hr0]; exact hp
    have hcB : range c ⊆ b.val.image := hcJ.trans hJb
    have hcg : range c ∩ range (g s)={g s 0,g s 1} := by
      apply Subset.antisymm
      · intro z hz
        exact (hg s).2.2.2 ▸ ⟨hz.2,hcB hz.1⟩
      · intro z hz
        rcases mem_insert_iff.mp hz with hz | hz
        · subst z; exact ⟨⟨0,hc0⟩,mem_range_self _⟩
        · subst z; exact ⟨⟨1,hc1⟩,mem_range_self _⟩
    have hcrossSide (t w : Interval) (he : c t=g s w) : (t=0 ∧ w=0) ∨ (t=1 ∧ w=1) := by
      have hz := hcg ▸ (show c t ∈ range c ∩ range (g s) from ⟨mem_range_self t,⟨w,he.symm⟩⟩)
      rcases mem_insert_iff.mp hz with hz | hz
      · exact Or.inl ⟨hc.injective (hz.trans hc0.symm),(hg s).1.injective (he.symm.trans hz)⟩
      · have hz := mem_singleton_iff.mp hz
        exact Or.inr ⟨hc.injective (hz.trans hc1.symm),(hg s).1.injective (he.symm.trans hz)⟩
    obtain ⟨curve,hcurve⟩ := CurveComplex.exists_curve_of_two_arcs c (g s) hc.injective (hg s).1.injective hc0 hc1 hcrossSide
    have hcurveD : curve.image ⊆ range d := by
      rw [hcurve]
      exact union_subset ((hcJ.trans hJN).trans interior_subset) ((hg s).2.1.trans interior_subset)
    obtain ⟨e,he,heb,heD⟩ := CurveComplex.LocalSurgery.curve_in_embedded_disk_bounds_subdisk curve d hd hcurveD
    exact ⟨u',v',c,g s,e,huv,huc,hvc,hc,(hg s).1,hc0,hc1,hcr,hpC,(hg s).2.2.1,
      (hg s).2.2.2,hcg,he,heb.trans hcurve,hdGraph.mono_left heD⟩
  have actual_raw_support_disk_move_fixes_entire_closed_obstacle_private
      (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
      (u z : S) (hf₀0 : f₀ 0=u) (hf₁0 : f₁ 0=u) (hf₀1 : f₀ 1=z) (hf₁1 : f₁ 1=z)
      (hinter : range f₀ ∩ range f₁={u,z})
      (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
      (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1}=range f₀ ∪ range f₁)
      (w : S) (hw : w ∉ range disk) (Q : Set S) (hQc : IsClosed Q)
      (hQboundary : ∀ y ∈ range f₀ ∪ range f₁,y ∈ Q → y=u ∨ y=z)
      (hQinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q) :
      ∃ H : AmbientIsotopy S,(∀ t y,y ∈ Q → H.map (t,y)=y) ∧
        H.finalMap '' range f₀=range f₁ := by
    letI : T2Space S := M.sphere.symm.t2Space
    letI : CompactSpace S := M.sphere.symm.compactSpace
    have embedded_side_isArcBetween (f : C(Interval,Plane))
        (hf : IsEmbedding f) : IsArcBetween (range f) (f 0) (f 1) := by
      let fc : ℝ → Plane := f ∘ Set.projIcc 0 1 zero_le_one
      have hfc : Continuous fc := f.continuous.comp continuous_projIcc
      have he (t : Interval) : fc t = f t := by
        simp [fc,Set.projIcc_of_mem zero_le_one t.property]
      refine ⟨fc,hfc.continuousOn,?_,?_,he 0,he 1⟩
      · intro t ht u hu h
        exact congrArg Subtype.val (hf.injective (by
          simpa only [← he] using h : f ⟨t,ht⟩ = f ⟨u,hu⟩))
      · ext x
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨⟨t,ht⟩,(he ⟨t,ht⟩).symm⟩
        · rintro ⟨t,rfl⟩
          exact ⟨t,t.property,he t⟩
    
    have hrawDiskChart (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
        (u0 z0 : S) (hf₀0 : f₀ 0=u0) (hf₁0 : f₁ 0=u0) (hf₀1 : f₀ 1=z0) (hf₁1 : f₁ 1=z0)
        (hinter : range f₀ ∩ range f₁ = {u0,z0})
        (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
        (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
        (w : S) (hw : w ∉ range disk) :
        ∃ (f : Plane → S) (A B : Set Plane) (p q : Plane),
          IsOpenEmbedding f ∧ IsArcBetween A p q ∧ IsArcBetween B p q ∧
          A ∪ B = modelCurve ∧ f '' A = range f₀ ∧ f '' B = range f₁ ∧
          f p=u0 ∧ f q=z0 ∧
          f '' Plane.openSquare 0 1 = disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1} := by
      classical
      letI : T2Space S := M.sphere.symm.t2Space
      let v := w
      have hv : v ∉ range disk := hw
      let e := M.puncturedPlane v
      let j : range disk → {z : S // z ≠ v} :=
        fun z => ⟨z.val,fun hz => hv (hz ▸ z.property)⟩
      let d : C(Metric.closedBall (0 : Plane) 1,Plane) :=
        ⟨fun x => e ⟨disk x,fun h => hv (h ▸ Set.mem_range_self x)⟩,by fun_prop⟩
      have firstDisk (t : Interval) : f₀ t ∈ range disk := by
        apply image_subset_range disk _
        rw [hboundary]
        exact Or.inl (Set.mem_range_self t)
      have secondDisk (t : Interval) : f₁ t ∈ range disk := by
        apply image_subset_range disk _
        rw [hboundary]
        exact Or.inr (Set.mem_range_self t)
      let g : C(Interval,Plane) :=
        ⟨fun t => e ⟨f₀ t,fun h => hv (h ▸ firstDisk t)⟩,by fun_prop⟩
      let h : C(Interval,Plane) :=
        ⟨fun t => e ⟨f₁ t,fun hh => hv (hh ▸ secondDisk t)⟩,by fun_prop⟩
      have hd : IsEmbedding d := (d.continuous.isClosedEmbedding (by
        intro x y hxy
        exact hdisk.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
      have hg : IsEmbedding g := (g.continuous.isClosedEmbedding (by
        intro x y hxy
        exact hf₀.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
      have hh : IsEmbedding h := (h.continuous.isClosedEmbedding (by
        intro x y hxy
        exact hf₁.injective (congrArg Subtype.val (e.injective hxy)))).isEmbedding
      have hg0 : g 0 = h 0 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀0.trans hf₁0.symm
      have hg1 : g 1 = h 1 := by apply e.injective.eq_iff.mpr; apply Subtype.ext; exact hf₀1.trans hf₁1.symm
      have hgA := embedded_side_isArcBetween g hg
      have hhB : IsArcBetween (range h) (g 0) (g 1) := by rw [hg0,hg1]; exact embedded_side_isArcBetween h hh
      have hc : IsJordanCurve (range g ∪ range h) := IsJordanCurve.of_two_arcs hgA hhB.reverse (by
        rintro z ⟨t,ht⟩ ⟨s,hs⟩
        have heq : f₀ t = f₁ s := congrArg Subtype.val (e.injective (ht.trans hs.symm))
        have hm : f₀ t ∈ ({u0,z0} : Set S) :=
          hinter ▸ ⟨Set.mem_range_self t,⟨s,heq.symm⟩⟩
        rcases mem_insert_iff.mp hm with hm | hm
        · left
          have ht0 : t=0 := hf₀.injective (hm.trans hf₀0.symm)
          exact ht.symm.trans (congrArg g ht0)
        · right
          have ht1 : t=1 := hf₀.injective ((mem_singleton_iff.mp hm).trans hf₀1.symm)
          exact ht.symm.trans (congrArg g ht1))
      have hbd : d '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range g ∪ range h := by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩
          have hxs : disk x ∈ range f₀ ∪ range f₁ := by
            rw [← hboundary]
            exact mem_image_of_mem disk hx
          rcases hxs with ⟨t,ht⟩ | ⟨t,ht⟩
          · left; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
          · right; refine ⟨t,?_⟩; apply congrArg e; apply Subtype.ext; exact ht
        · rintro (⟨t,rfl⟩ | ⟨t,rfl⟩)
          · have htB : f₀ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
              rw [hboundary]; exact Or.inl (Set.mem_range_self t)
            obtain ⟨x,hx,hxt⟩ := htB
            refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
          · have htB : f₁ t ∈ disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} := by
              rw [hboundary]; exact Or.inr (Set.mem_range_self t)
            obtain ⟨x,hx,hxt⟩ := htB
            refine ⟨x,hx,?_⟩; apply congrArg e; apply Subtype.ext; exact hxt
      have hrange := CurveComplex.embedded_disc_range_eq_closed_inside d hd _ hc hbd
      have hi : d '' {x | x.val ∈ Metric.ball (0 : Plane) 1} = inside (range g ∪ range h) := by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩
          rcases hrange ▸ Set.mem_range_self x with hi | hb
          · exact hi
          · obtain ⟨y,hy,hyx⟩ := hbd.symm ▸ hb
            have he := congrArg Subtype.val (hd.injective hyx)
            have hyxS : x.val ∈ Metric.sphere (0 : Plane) 1 := he ▸ hy
            have hnlt : ‖x.val‖ < (1 : ℝ) := by
              change dist x.val 0 < 1 at hx
              simpa only [dist_zero_right] using hx
            have hneq : ‖x.val‖ = (1 : ℝ) := by
              change dist x.val 0 = 1 at hyxS
              simpa only [dist_zero_right] using hyxS
            exact False.elim (ne_of_lt hnlt hneq)
        · intro hz
          have hzR : z ∈ range d := by rw [hrange]; exact Or.inl hz
          obtain ⟨x,hx⟩ := hzR
          refine ⟨x,?_,hx⟩
          have hn : ‖x.val‖ ≤ (1 : ℝ) := by
            simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
          have hnb : x.val ∉ Metric.sphere (0 : Plane) 1 := by
            intro hxb
            have hzB : z ∈ range g ∪ range h := by rw [← hbd,← hx]; exact mem_image_of_mem d hxb
            exact Set.disjoint_right.mp (disjoint_curve_inside _) hz hzB
          change dist x.val 0 < 1
          rw [dist_zero_right]
          exact lt_of_le_of_ne hn (by simpa only [Metric.mem_sphere,dist_zero_right] using hnb)
      obtain ⟨ec⟩ := IsJordanCurve.modelCurve_homeomorph hc
      obtain ⟨φ,hφ⟩ := jordan_schoenflies_of_homeomorph isJordanCurve_modelCurve hc ec
      have hφC : φ '' modelCurve = range g ∪ range h := by
        ext z
        constructor
        · rintro ⟨x,hx,rfl⟩; rw [hφ ⟨x,hx⟩]; exact (ec ⟨x,hx⟩).property
        · intro hz
          let x := ec.symm ⟨z,hz⟩
          refine ⟨x.val,x.property,?_⟩
          rw [hφ x]; exact congrArg Subtype.val (ec.apply_symm_apply _)
      have hφI : φ '' Plane.openSquare 0 1 = inside (range g ∪ range h) := by
        rw [← inside_modelCurve]
        simpa only [hφC] using CurveComplex.jordan_inside_homeomorph_image φ modelCurve
      let f : Plane → S := M.planeToSphere v ∘ φ
      let A := φ.symm '' range g
      let B := φ.symm '' range h
      let p := φ.symm (g 0)
      let q := φ.symm (g 1)
      have hcancel (K : Set Plane) : φ '' (φ.symm '' K) = K := by
        ext z; simp
      have hgs (t) : M.planeToSphere v (g t) = f₀ t := congrArg Subtype.val (e.symm_apply_apply _)
      have hhs (t) : M.planeToSphere v (h t) = f₁ t := congrArg Subtype.val (e.symm_apply_apply _)
      refine ⟨f,A,B,p,q,(M.planeToSphere_isOpenEmbedding v).comp φ.isOpenEmbedding,
        hgA.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,
        hhB.image_of_injOn (Set.subset_univ _) φ.symm.continuous.continuousOn φ.symm.injective.injOn,?_,?_,?_,?_,?_,?_⟩
      · change φ.symm '' range g ∪ φ.symm '' range h = modelCurve
        rw [← image_union,← hφC]
        ext z; simp
      · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range g) = _
        rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hgs)
      · change (M.planeToSphere v ∘ φ) '' (φ.symm '' range h) = _
        rw [image_comp,hcancel,← range_comp]; exact congrArg range (funext hhs)
      · change M.planeToSphere v (φ (φ.symm (g 0))) = _
        rw [φ.apply_symm_apply,hgs,hf₀0]
      · change M.planeToSphere v (φ (φ.symm (g 1))) = _
        rw [φ.apply_symm_apply,hgs,hf₀1]
      · change (M.planeToSphere v ∘ φ) '' Plane.openSquare 0 1 = _
        rw [image_comp,hφI,← hi,image_image]
        apply Set.image_congr
        intro x hx
        exact congrArg Subtype.val (e.symm_apply_apply _)
    have hrelativeRawDiskMove
        (f₀ f₁ : C(Interval,S)) (hf₀ : IsEmbedding f₀) (hf₁ : IsEmbedding f₁)
        (u z : S) (hf₀0 : f₀ 0=u) (hf₁0 : f₁ 0=u) (hf₀1 : f₀ 1=z) (hf₁1 : f₁ 1=z)
        (hinter : range f₀ ∩ range f₁ = {u,z})
        (disk : C(Metric.closedBall (0 : Plane) 1,S)) (hdisk : IsEmbedding disk)
        (hboundary : disk '' {x | x.val ∈ Metric.sphere (0 : Plane) 1} = range f₀ ∪ range f₁)
        (w : S) (hw : w ∉ range disk)
        (Q : Set S) (hQc : IsClosed Q)
        (hQboundary : ∀ y ∈ range f₀ ∪ range f₁, y ∈ Q → y=u ∨ y=z)
        (hQinside : Disjoint (disk '' {x | x.val ∈ Metric.ball (0 : Plane) 1}) Q) :
        ∃ H : CurveComplex.AmbientIsotopy S,
          (∀ t y, y ∈ Q → H.map (t,y)=y) ∧ H.finalMap '' range f₀ = range f₁ := by
      obtain ⟨F,A,B,p,q,hF,hA,hB,hwhole,hFA,hFB,hFp,hFq,hFI⟩ :=
        hrawDiskChart f₀ f₁ hf₀ hf₁ u z hf₀0 hf₁0 hf₀1 hf₁1 hinter disk hdisk hboundary w hw
      have hb : ∀ x ∈ modelCurve, F x ∈ Q → x=p ∨ x=q := by
        intro x hx hxQ
        have hxB : F x ∈ range f₀ ∪ range f₁ := by
          rw [← hFA,← hFB,← image_union,hwhole]
          exact mem_image_of_mem F hx
        rcases hQboundary (F x) hxB hxQ with hxu | hxz
        · exact Or.inl (hF.injective (hxu.trans hFp.symm))
        · exact Or.inr (hF.injective (hxz.trans hFq.symm))
      obtain ⟨H,hfix,hmove⟩ := CurveComplex.actual_raw_bigon_supported_replacement F hF A B p q
        hA hB hwhole Q hQc hb (by rwa [hFI])
      exact ⟨H,hfix,by simpa only [hFA,hFB] using hmove⟩
    exact hrelativeRawDiskMove f₀ f₁ hf₀ hf₁ u z hf₀0 hf₁0 hf₀1 hf₁1 hinter disk hdisk
      hboundary w hw Q hQc hQboundary hQinside
  have actual_original_inner_empty_disk_graph_fixed_strict_whole_contact_drop
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (h0 : D.firstCorner ∉ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hDG : Disjoint D.openInterior (actualObjectTrace M r J))
      (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (rT u).val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').Finite ∧
        (∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b',
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) b' p) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').ncard <
          (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨u₀,v₀,c,g,e,huv,hu₀,hv₀,hc,hg,hc0,hc1,hcr,hremoved,hgA,hgB,hcg,he,heb,heGraph⟩ :=
      actual_original_inner_disk_produces_graph_clear_supporting_old_core
        D h0 h1 hempty hDG hcross
    have heMarks : Disjoint (range e) (M.cover.branch:Set S) := heGraph.mono_right subset_union_left
    obtain ⟨R,hR,hOld,hCR,hRfree,hInsideR⟩ :=
      actual_essential_mark_free_support_disk_retained_remainder
        a b u₀ v₀ c g hu₀ hv₀ hcr hgA hgB e he heb heMarks
    have hRb : R ⊆ b.val.image := hOld.symm ▸ subset_union_right
    have hBoundaryE : range c ∪ range g ⊆ range e := by
      rw [←heb]; exact image_subset_range _ _
    let Q : Set S := ((M.cover.branch:Set S) ∪ actualObjectTrace M r J) ∪ R
    have hQ : IsClosed Q := (M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed).union hR.isClosed
    have hQboundary : ∀ z ∈ range c ∪ range g,z ∈ Q → z=g 0 ∨ z=g 1 := by
      intro z hz hzQ
      rcases hzQ with hzQ | hzR
      · exact False.elim (disjoint_left.mp heGraph (hBoundaryE hz) hzQ)
      · rcases hz with hzC | hzG
        · exact hCR z ⟨hzC,hzR⟩
        · have hp : z ∈ ({g 0,g 1}:Set S) := hgB ▸ ⟨hzG,hRb hzR⟩
          simpa only [mem_insert_iff,mem_singleton_iff] using hp
    have hQinside : Disjoint (e '' {x | x.val ∈ Metric.ball (0:Plane) 1}) Q :=
      (heGraph.mono_left (image_subset_range _ _)).union_right hInsideR
    have hw : b.val.map (0:Interval) ∉ range e :=
      fun hp => disjoint_left.mp heMarks hp b.val.start_marked
    obtain ⟨H,hfix,hmove⟩ := actual_raw_support_disk_move_fixes_entire_closed_obstacle_private
      c g hc hg (g 0) (g 1) hc0 rfl hc1 rfl hcg e he heb (b.val.map 0) hw
      Q hQ hQboundary hQinside
    have hRimage : H.finalMap '' R=R := by
      apply Subset.antisymm
      · rintro z ⟨x,hx,rfl⟩
        have heq := hfix 1 x (Or.inr hx)
        change H.finalMap x=x at heq
        rw [heq]; exact hx
      · intro z hz
        exact ⟨z,hz,hfix 1 z (Or.inr hz)⟩
    have hNew : H.finalMap '' b.val.image=range g ∪ R := by
      rw [hOld,image_union,hmove,hRimage]
    have hrm : (ArcSurgery.crossings M a b ∩ range c).Nonempty :=
      ⟨D.firstCorner,⟨⟨D.first_on_curve ⟨0,D.first_zero⟩,h0⟩,
        D.second_on_curve ⟨0,D.second_zero⟩,h0⟩,hremoved⟩
    have hm : ∀ t z,z ∈ M.cover.branch → H.map (t,z)=z :=
      fun t z hz => hfix t z (Or.inl (Or.inl hz))
    obtain ⟨b',himage,hclass,hends,hfin,htrans,hdrop⟩ :=
      actual_essential_closed_piece_strict_drop_assembly a b hfinite hcross H hm
        (range c) (range g) R (isCompact_range c.continuous) (isCompact_range g.continuous)
        hOld hNew (hgA.mono_right inter_subset_left) hRfree hrm
    exact ⟨b',H,hm,(fun t z hz => hfix t z (Or.inl (Or.inr hz))),
      himage,hclass,hfin,htrans,hdrop⟩
  have actual_original_marked_half_disk_graph_fixed_strict_whole_contact_drop_private
      (D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u))
      (hbase : D.firstCorner ∈ M.cover.branch) (h1 : D.secondCorner ∉ M.cover.branch)
      (hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image))
      (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p) :
      ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (rT u).val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').Finite ∧
        (∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b',
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) b' p) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').ncard <
          (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard := by
    classical
    letI : T2Space S := M.sphere.symm.t2Space
    let a := r0 ⟨u.val,hTF u.property⟩
    let b := rT u
    obtain ⟨c,g,R,d,hc,hg,hd,hc0,hg0,hc1,hcb,hpC,hcg,hgA,hgB,hgQ,hcQ,
      hR,hOld,hCR,hretain,hgfree,hboundary,hcorner,hmarks,hgraph,hexterior⟩ :=
      actual_original_marked_half_disk_actual_core_support_disk_private D hbase h1 hempty hcross
    have hRb : R ⊆ b.val.image := hOld.symm ▸ subset_union_right
    let Q : Set S := ((M.cover.branch:Set S) ∪ actualObjectTrace M r J) ∪ R
    have hQ : IsClosed Q := (M.cover.branch.finite_toSet.isClosed.union
      (actualObjectTrace_compact M r J).isClosed).union hR.isClosed
    have hQboundary : ∀ z ∈ range c ∪ range g,z ∈ Q → z=D.firstCorner ∨ z=g 1 := by
      intro z hz hzQ
      rcases hzQ with hzQ | hzR
      · left
        rcases hz with hzC | hzG
        · exact mem_singleton_iff.mp (hcQ ▸ ⟨hzC,hzQ⟩)
        · exact mem_singleton_iff.mp (hgQ ▸ ⟨hzG,hzQ⟩)
      · have hh : z ∈ ({D.firstCorner,g 1}:Set S) := by
          rcases hz with hzC | hzG
          · exact hCR ▸ ⟨hzC,hzR⟩
          · exact hgB ▸ ⟨hzG,hRb hzR⟩
        simpa only [mem_insert_iff,mem_singleton_iff] using hh
    have hQinside : Disjoint (d '' {x | x.val ∈ Metric.ball (0:Plane) 1}) Q :=
      (hmarks.union_right hgraph).union_right (hexterior.mono_right hRb)
    have hcard : ({D.firstCorner}:Finset S).card<M.cover.branch.card := by
      rw [M.cover.branch_card]; simp
    obtain ⟨w,hwM,hwNe⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
    have hw : w ∉ range d := by
      intro hw
      exact hwNe (by simpa only [Finset.mem_singleton] using hcorner w hw hwM)
    obtain ⟨H,hfix,hmove⟩ := actual_raw_support_disk_move_fixes_entire_closed_obstacle_private
      c g hc hg D.firstCorner (g 1) hc0 hg0 hc1 rfl hcg d hd hboundary w hw Q hQ hQboundary hQinside
    have hRimage : H.finalMap '' R=R := by
      apply Subset.antisymm
      · rintro z ⟨x,hx,rfl⟩
        have heq := hfix 1 x (Or.inr hx)
        change H.finalMap x=x at heq
        rw [heq]; exact hx
      · intro z hz
        exact ⟨z,hz,hfix 1 z (Or.inr hz)⟩
    have hNew : H.finalMap '' b.val.image=range g ∪ R := by
      rw [hOld,image_union,hmove,hRimage]
    have hBfree : Disjoint (range g) (arcInterior M a) := by
      apply disjoint_left.mpr
      intro z hzG hzA
      have he : z=D.firstCorner := mem_singleton_iff.mp (hgA ▸ ⟨hzG,hzA.1⟩)
      exact hzA.2 (he.symm ▸ hbase)
    have hrm : (ArcSurgery.crossings M a b ∩ range c).Nonempty :=
      ⟨D.secondCorner,⟨⟨D.first_on_curve ⟨1,D.first_one⟩,h1⟩,
        D.second_on_curve ⟨1,D.second_one⟩,h1⟩,hpC⟩
    have hm : ∀ t z,z ∈ M.cover.branch → H.map (t,z)=z :=
      fun t z hz => hfix t z (Or.inl (Or.inl hz))
    obtain ⟨b',himage,hclass,hends,hfin,htrans,hdrop⟩ :=
      actual_essential_closed_piece_strict_drop_assembly a b hfinite hcross H hm
        (range c) (range g) R (isCompact_range c.continuous) (isCompact_range g.continuous)
        hOld hNew hBfree hretain hrm
    exact ⟨b',H,hm,(fun t z hz => hfix t z (Or.inl (Or.inr hz))),
      himage,hclass,hfin,htrans,hdrop⟩
  have actual_original_positive_nonloop_source_strict_drop_or_marked_half_disk
      (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
        (r0 ⟨u.val,hTF u.property⟩).val.map 1)
      (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p)
      (p : S) (hp : p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
      (∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (rT u).val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').Finite ∧
        (∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b',
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) b' q) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').ncard <
          (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard) ∨
      (∃ D : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        Disjoint D.openInterior
          ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image ∪
            (M.cover.branch : Set S) ∪ actualObjectTrace M r J) ∧
        (D.firstCorner ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u) ∨
          D.secondCorner ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) ∧
        (D.firstCorner ∈ M.cover.branch ∨ D.secondCorner ∈ M.cover.branch)) := by
    obtain ⟨D,hDfree,hDcontact⟩ :=
      actual_selected_original_loop_entire_pair_and_graph_clear_disk ha hfinite hcross p hp
    by_cases h0 : D.firstCorner ∈ M.cover.branch
    · exact Or.inr ⟨D,hDfree,hDcontact,Or.inl h0⟩
    by_cases h1 : D.secondCorner ∈ M.cover.branch
    · exact Or.inr ⟨D,hDfree,hDcontact,Or.inr h1⟩
    apply Or.inl
    exact actual_original_inner_empty_disk_graph_fixed_strict_whole_contact_drop
      D h0 h1 (hDfree.mono_right (fun z hz => Or.inl (Or.inl hz)))
      (hDfree.mono_right subset_union_right) hfinite hcross
  have actual_original_positive_nonloop_source_graph_fixed_strict_whole_contact_drop_private
      (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
        (r0 ⟨u.val,hTF u.property⟩).val.map 1)
      (hfinite : (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).Finite)
      (hcross : ∀ p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u),
        ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) p)
      (p : S) (hp : p ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)) :
      ∃ b' : EssentialMarkedArc M,∃ H : AmbientIsotopy S,
        (∀ t z,z ∈ M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z,z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (rT u).val.image=b'.val.image ∧
        Quotient.mk (essentialArcSetoid M) b'=Quotient.mk (essentialArcSetoid M) (rT u) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').Finite ∧
        (∀ q ∈ ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b',
          ArcSurgery.CrossesInDisk M (r0 ⟨u.val,hTF u.property⟩) b' q) ∧
        (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) b').ncard <
          (ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)).ncard := by
    obtain ⟨D,hDfree,hDcontact⟩ :=
      actual_selected_original_loop_entire_pair_and_graph_clear_disk ha hfinite hcross p hp
    have hempty : Disjoint D.openInterior
        ((r0 ⟨u.val,hTF u.property⟩).val.image ∪ (rT u).val.image) :=
      hDfree.mono_right (fun z hz => Or.inl (Or.inl hz))
    by_cases h0 : D.firstCorner ∈ M.cover.branch
    · have h1 : D.secondCorner ∉ M.cover.branch := by
        rcases hDcontact with hc | hc
        · exact False.elim (hc.1.2 h0)
        · exact hc.1.2
      exact actual_original_marked_half_disk_graph_fixed_strict_whole_contact_drop_private
        D h0 h1 hempty hfinite hcross
    by_cases h1 : D.secondCorner ∈ M.cover.branch
    · let rev (f : C(Interval,S)) : C(Interval,S) :=
        ⟨fun t => f (unitInterval.symm t),f.continuous.comp unitInterval.continuous_symm⟩
      have hrange (f : C(Interval,S)) : range (rev f)=range f :=
        unitInterval.symmHomeomorph.surjective.range_comp f
      let D' : ActualMarkedTwoSideDisk M (r0 ⟨u.val,hTF u.property⟩) (rT u) := {
        firstCorner := D.secondCorner
        secondCorner := D.firstCorner
        firstSide := rev D.firstSide
        secondSide := rev D.secondSide
        first_embedded := D.first_embedded.comp unitInterval.symmHomeomorph.isEmbedding
        second_embedded := D.second_embedded.comp unitInterval.symmHomeomorph.isEmbedding
        first_zero := by simpa only [rev,ContinuousMap.coe_mk,unitInterval.symm_zero] using D.first_one
        first_one := by simpa only [rev,ContinuousMap.coe_mk,unitInterval.symm_one] using D.first_zero
        second_zero := by simpa only [rev,ContinuousMap.coe_mk,unitInterval.symm_zero] using D.second_one
        second_one := by simpa only [rev,ContinuousMap.coe_mk,unitInterval.symm_one] using D.second_zero
        first_on_curve := by rw [hrange]; exact D.first_on_curve
        second_on_curve := by rw [hrange]; exact D.second_on_curve
        sides_inter := by rw [hrange,hrange,D.sides_inter]; exact Set.pair_comm _ _
        disk := D.disk
        disk_embedded := D.disk_embedded
        boundary_eq := by rw [hrange,hrange]; exact D.boundary_eq
        marks_are_corners := by
          intro z hz hzm
          simpa only [Set.pair_comm] using D.marks_are_corners z hz hzm }
      exact actual_original_marked_half_disk_graph_fixed_strict_whole_contact_drop_private
        D' h1 h0 hempty hfinite hcross
    exact actual_original_inner_empty_disk_graph_fixed_strict_whole_contact_drop
      D h0 h1 hempty (hDfree.mono_right subset_union_right) hfinite hcross
  exact actual_original_positive_nonloop_source_graph_fixed_strict_whole_contact_drop_private ha hfinite hcross q hq

#print axioms actual_original_nonloop_given_graph_clear_disk_strict_contact_drop_private
end CurveComplex.HyperellipticModel
