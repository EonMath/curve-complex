import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopFinitePreparationFullTargetPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGraphClearDiskConditionalFullTargetPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalLoopUnconditionalZeroContactFullTargetProducerPrivate
import CurveComplexGenusTwo.Topology.ActualSelectedLoopStrip.SelectedLoopPinchedStripLeafRequest
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
open Set Metric Topology Schoenflies
open CurveGenusTwo.Filtration CategoryTheory
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2600000
private theorem actual_original_zero_contact_nonloop_graph_relative_alignment_private
    (M : HyperellipticModel E S) (p : ℕ) (T : ActualStratum M p)
    (F J : Finset (EssentialArcClass M)) (hTF : T.val⊆F) (hJT : J⊆T.val)
    (r r0 : {w//w∈F} → EssentialMarkedArc M)
    (hr0 : ∀ w,Quotient.mk (essentialArcSetoid M) (r0 w)=w.val)
    (hd0 : ∀ w z,w≠z → Disjoint (arcInterior M (r0 w)) (arcInterior M (r0 z)))
    (rT : {w//w∈T.val} → EssentialMarkedArc M)
    (hrT : ∀ w,Quotient.mk (essentialArcSetoid M) (rT w)=w.val)
    (hdT : ∀ w z,w≠z → Disjoint (arcInterior M (rT w)) (arcInterior M (rT z)))
    (haligned0 : ∀ w : {w//w∈T.val},w.val∈J → r0 ⟨w.val,hTF w.property⟩=rT w)
    (hgraph : actualObjectTrace M r0 J=actualObjectTrace M r J)
    (u : {w//w∈T.val}) (hu : u.val∉J)
    (ha : (r0 ⟨u.val,hTF u.property⟩).val.map 0≠
      (r0 ⟨u.val,hTF u.property⟩).val.map 1)

    (hzero : ArcSurgery.crossings M (r0 ⟨u.val,hTF u.property⟩) (rT u)=∅) :
    ∃ K : AmbientIsotopy S,
      (∀ t z,z∈M.cover.branch → K.map (t,z)=z) ∧
      (∀ t z,z∈actualObjectTrace M r J → K.map (t,z)=z) ∧
      K.finalMap '' (r0 ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image := by
  classical
  have actual_endpoint_enlargement_retains_entire_old_interior
      (A B : Set Plane) (p q : Plane) (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
      (hwhole : A ∪ B=modelCurve) (F : Set Plane) (hF : IsClosed F)
      (hpF : p ∈ F) (hqF : q ∈ F)
      (hboundary : ∀ z ∈ F, z ∈ modelCurve → z=p ∨ z=q)
      (hinside : Disjoint (Plane.openSquare 0 1) F) :
      ∃ φ : Plane ≃ₜ Plane,
        φ p=p ∧ φ q=q ∧
        IsArcBetween (φ.symm '' A) p q ∧ IsArcBetween (φ.symm '' B) p q ∧
        (φ.symm '' A) \ {p,q} ⊆ Plane.openSquare 0 1 ∧
        (φ.symm '' B) \ {p,q} ⊆ Plane.openSquare 0 1 ∧
        (∀ z ∈ Plane.openSquare 0 1, φ z ∉ F) ∧
        φ.symm '' Plane.openSquare 0 1 ⊆ Plane.openSquare 0 1 := by
    obtain ⟨φ,hp,hq,hA',hB',hAi,hBi,hfree⟩ :=
      actual_endpoint_preserving_bigon_enlargement A B p q hA hB hwhole F hF hpF hqF hboundary hinside
    have hpC : p ∈ modelCurve := hwhole ▸ Or.inl hA.left_mem
    have hqC : q ∈ modelCurve := hwhole ▸ Or.inl hA.right_mem
    have hpQ : p ∈ Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr hpC.le
    have hqQ : q ∈ Plane.closedSquare 0 1 := mem_closedSquare_zero_one.mpr hqC.le
    have hcurve : φ.symm '' modelCurve ⊆ Plane.closedSquare 0 1 := by
      rintro z ⟨u,hu,rfl⟩
      by_cases hup : φ.symm u=p
      · exact hup.symm ▸ hpQ
      by_cases huq : φ.symm u=q
      · exact huq.symm ▸ hqQ
      have hnot : φ.symm u ∉ ({p,q} : Set Plane) := by simp only [Set.mem_insert_iff,Set.mem_singleton_iff]; exact not_or.mpr ⟨hup,huq⟩
      have huAB : u ∈ A ∪ B := hwhole.symm ▸ hu
      have hunit : φ.symm u ∈ Plane.openSquare 0 1 := by
        rcases huAB with huA | huB
        · exact hAi ⟨⟨u,huA,rfl⟩,hnot⟩
        · exact hBi ⟨⟨u,huB,rfl⟩,hnot⟩
      exact mem_closedSquare_zero_one.mpr (mem_openSquare_zero_one.mp hunit).le
    have hinterior := actual_jordan_inside_closed_square
      (jordan_curve_homeomorph_image isJordanCurve_modelCurve φ.symm) hcurve
    rw [←jordan_inside_homeomorph_image,inside_modelCurve] at hinterior
    exact ⟨φ,hp,hq,hA',hB',hAi,hBi,hfree,hinterior⟩

  have actual_terminal_empty_bigon_contained_nonloop_arc_class
      (a c : EssentialMarkedArc M) (hcne : c.val.map (0 : Interval) ≠ c.val.map 1)
      (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
      (A B : Set Plane) (p q : Plane)
      (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
      (hwhole : A ∪ B=modelCurve) (haImage : a.val.image=f '' A)
      (hpmark : f p ∈ M.cover.branch) (hqmark : f q ∈ M.cover.branch)
      (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z=p ∨ z=q)
      (hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch)
      (hcImage : c.val.image ⊆ f '' Plane.closedSquare 0 1)
      (hcInterior : arcInterior M c ⊆ f '' Plane.openSquare 0 1) :
      Quotient.mk (essentialArcSetoid M) a=Quotient.mk (essentialArcSetoid M) c := by
    let e : Plane ≃ₜ Set.range f := hf.toIsEmbedding.toHomeomorph
    have hcSource (t : Interval) : c.val.map t ∈ Set.range f := by
      obtain ⟨z,hz,he⟩ := hcImage (Set.mem_range_self t)
      exact ⟨z,he⟩
    let γ : C(Interval,Plane) := ⟨fun t => e.symm ⟨c.val.map t,hcSource t⟩,
      e.symm.continuous.comp (c.val.continuous.subtype_mk hcSource)⟩
    have hcoord (t : Interval) : f (γ t)=c.val.map t := by
      change (e (e.symm ⟨c.val.map t,hcSource t⟩)).val=c.val.map t
      rw [e.apply_symm_apply]
    have hγi : Function.Injective γ := by
      intro s t he
      apply (show Function.Injective c.val.map from NonLoopArc.injective (⟨c.val,hcne⟩ : NonLoopArc M))
      exact (hcoord s).symm.trans ((congrArg f he).trans (hcoord t))
    have hγSquare (t : Interval) : γ t ∈ Plane.closedSquare 0 1 := by
      obtain ⟨z,hz,he⟩ := hcImage (Set.mem_range_self t)
      have hzγ : z=γ t := hf.injective (he.trans (hcoord t).symm)
      exact hzγ ▸ hz
    have hends (t : Interval) (ht : t=0 ∨ t=1) : γ t=p ∨ γ t=q := by
      have hmarked : f (γ t) ∈ M.cover.branch := by
        rw [hcoord]
        rcases ht with rfl | rfl
        · exact c.val.start_marked
        · exact c.val.end_marked
      have hcurve : γ t ∈ modelCurve := by
        have hsq := hγSquare t
        rw [←modelCurve_union_inside] at hsq
        rcases hsq with hcurve | hi
        · exact hcurve
        · exact False.elim (hfree _ (inside_modelCurve ▸ hi) hmarked)
      exact hboundary _ hcurve hmarked
    have hends0 := hends 0 (Or.inl rfl)
    have hends1 := hends 1 (Or.inr rfl)
    have hγne : γ 0≠γ 1 := fun he => hcne ((hcoord 0).symm.trans
      ((congrArg f he).trans (hcoord 1)))
    let C : Set Plane := Set.range γ
    have hCraw : IsArcBetween C (γ 0) (γ 1) := by
      let realγ : ℝ → Plane := γ ∘ Set.projIcc 0 1 zero_le_one
      refine ⟨realγ,(γ.continuous.comp continuous_projIcc).continuousOn,?_,?_,?_,?_⟩
      · intro s hs t ht he
        have hγ : γ ⟨s,hs⟩=γ ⟨t,ht⟩ := by
          simpa only [realγ,Function.comp_apply,Set.projIcc_of_mem zero_le_one hs,
            Set.projIcc_of_mem zero_le_one ht] using he
        exact congrArg Subtype.val (hγi hγ)
      · ext z
        constructor
        · rintro ⟨t,ht,rfl⟩
          exact ⟨Set.projIcc 0 1 zero_le_one t,rfl⟩
        · rintro ⟨t,rfl⟩
          refine ⟨t.val,t.property,?_⟩
          simp only [realγ,Function.comp_apply,Set.projIcc_val]
      · change γ (Set.projIcc 0 1 zero_le_one (0:ℝ))=γ (0:Interval)
        apply congrArg γ
        apply Subtype.ext
        simp [Set.projIcc]
      · change γ (Set.projIcc 0 1 zero_le_one (1:ℝ))=γ (1:Interval)
        apply congrArg γ
        apply Subtype.ext
        simp [Set.projIcc]
    have hC : IsArcBetween C p q := by
      rcases hends0 with h0 | h0 <;> rcases hends1 with h1 | h1
      · exact False.elim (hγne (h0.trans h1.symm))
      · simpa only [h0,h1] using hCraw
      · simpa only [h0,h1] using hCraw.reverse
      · exact False.elim (hγne (h0.trans h1.symm))
    have hCproper : C \ {p,q} ⊆ Plane.openSquare 0 1 := by
      rintro z ⟨⟨t,rfl⟩,hn⟩
      have hmark : f (γ t) ∉ M.cover.branch := by
        intro hm
        have hmt : c.val.map t ∈ M.cover.branch := hcoord t ▸ hm
        rcases c.val.marked_only_at_ends t hmt with ht | ht
        · exact hn (by rcases hends0 with hp | hq
                       · exact Or.inl (ht ▸ hp)
                       · exact Or.inr (Set.mem_singleton_iff.mpr (ht ▸ hq)))
        · exact hn (by rcases hends1 with hp | hq
                       · exact Or.inl (ht ▸ hp)
                       · exact Or.inr (Set.mem_singleton_iff.mpr (ht ▸ hq)))
      have hcin : f (γ t) ∈ arcInterior M c := ⟨⟨t,(hcoord t).symm⟩,hmark⟩
      obtain ⟨w,hw,he⟩ := hcInterior hcin
      exact hf.injective he ▸ hw
    have hcimage : c.val.image=f '' C := by
      ext z
      constructor
      · rintro ⟨t,rfl⟩
        exact ⟨γ t,Set.mem_range_self t,hcoord t⟩
      · rintro ⟨w,⟨t,rfl⟩,rfl⟩
        exact ⟨t,(hcoord t).symm⟩
    let F : Set Plane := f ⁻¹' (M.cover.branch : Set S)
    have hFc : IsClosed F := by
      letI : T2Space S := M.sphere.symm.t2Space
      exact M.cover.branch.finite_toSet.isClosed.preimage hf.continuous
    have hFi : Disjoint (Plane.openSquare 0 1) F :=
      Set.disjoint_left.mpr (fun z hz hzF => hfree z hz hzF)
    obtain ⟨φ,hφp,hφq,hA',hB',hAi,hBi,hfree',hretain⟩ :=
      actual_endpoint_enlargement_retains_entire_old_interior A B p q hA hB hwhole F hFc
        hpmark hqmark (fun z hz hzC => hboundary z hzC hz) hFi
    have hφip : φ.symm p=p := by apply φ.injective; rw [φ.apply_symm_apply,hφp]
    have hφiq : φ.symm q=q := by apply φ.injective; rw [φ.apply_symm_apply,hφq]
    have hC' : IsArcBetween (φ.symm '' C) p q := by
      simpa only [hφip,hφiq] using hC.image_of_injOn (Set.subset_univ _)
        φ.symm.continuous.continuousOn φ.symm.injective.injOn
    have hCi : (φ.symm '' C) \ {p,q} ⊆ Plane.openSquare 0 1 := by
      rintro z ⟨⟨w,hw,rfl⟩,hn⟩
      have hnot : w ∉ ({p,q}:Set Plane) := by
        intro hh
        rcases hh with hh | hh
        · exact hn (Or.inl (by rw [hh,hφip]))
        · exact hn (Or.inr (Set.mem_singleton_iff.mpr (by rw [Set.mem_singleton_iff.mp hh,hφiq])))
      exact hretain ⟨w,hCproper ⟨hw,hnot⟩,rfl⟩
    have hcancel (D : Set Plane) : (f ∘ φ) '' (φ.symm '' D)=f '' D := by
      rw [Set.image_image]
      simp only [Function.comp_apply,φ.apply_symm_apply]
    have havoid : ∀ z ∈ Plane.openSquare 0 1,
        (f ∘ φ) z ∉ M.cover.branch ∧ (f ∘ φ) z ∉ (∅:Set S) := by
      intro z hz
      exact ⟨hfree' z hz,by simp⟩
    obtain ⟨H,hm,hP,himage⟩ := actual_crosscut_isotopy_fixing_graph M (∅:Set S) a c
      (f ∘ φ) (hf.comp φ.isOpenEmbedding) (φ.symm '' A) (φ.symm '' C) p q hA' hC'
      (hwhole ▸ Or.inl hA.left_mem) (hwhole ▸ Or.inl hA.right_mem) hAi hCi
      (haImage.trans (hcancel A).symm) (hcimage.trans (hcancel C).symm) havoid
    exact Quotient.sound ⟨H,hm,himage⟩

  have actual_terminal_prescribed_bigon_avoids_entire_aligned_graph
      (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
      (r : {w // w ∈ F} → EssentialMarkedArc M)
      (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w)=w.val)
      (hd : ∀ w z, w≠z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
      (haligned : ∀ w : {w // w ∈ T.val}, w.val ∈ J → r ⟨w.val,hTF w.property⟩=rT w)
      (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
      (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
      (A B : Set Plane) (p q : Plane)
      (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
      (hwhole : A ∪ B=modelCurve)
      (haImage : (r ⟨u.val,hTF u.property⟩).val.image=f '' A)
      (hbImage : (rT u).val.image=f '' B)
      (hpmark : f p ∈ M.cover.branch) (hqmark : f q ∈ M.cover.branch)
      (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z=p ∨ z=q)
      (hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hdisk : Topology.IsEmbedding d)
      (hdimage : Set.range d=f '' Plane.closedSquare 0 1)
      (hdmarks : Disjoint
        (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S)) :
      Disjoint (f '' Plane.openSquare 0 1) (actualObjectTrace M r J) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨y,hy,rfl⟩ hzG
    obtain ⟨w,hw⟩ := Set.mem_iUnion.mp hzG
    obtain ⟨hwJ,hzw⟩ := Set.mem_iUnion.mp hw
    let uF : {w // w ∈ F} := ⟨u.val,hTF u.property⟩
    let wT : {w // w ∈ T.val} := ⟨w.val,hJT hwJ⟩
    have hwuF : w≠uF := by
      intro he
      apply hu
      have hval : w.val=u.val := congrArg Subtype.val he
      exact hval ▸ hwJ
    have hwuT : wT≠u := by
      intro he
      apply hu
      have hval : w.val=u.val := congrArg Subtype.val he
      exact hval ▸ hwJ
    have heF : (⟨wT.val,hTF wT.property⟩ : {w // w ∈ F})=w := Subtype.ext rfl
    have hrw : r w=rT wT := by
      simpa only [heF] using haligned wT hwJ
    have hwb : Disjoint (arcInterior M (r w)) (arcInterior M (rT u)) := by
      rw [hrw]
      exact hdT wT u hwuT
    have hboundaryImage : (r uF).val.image ∪ (rT u).val.image=f '' modelCurve := by
      rw [haImage,hbImage,←Set.image_union,hwhole]
    have hentry : (arcInterior M (r w) ∩ f '' Plane.openSquare 0 1).Nonempty :=
      ⟨f y,⟨hzw,hfree y hy⟩,⟨y,hy,rfl⟩⟩
    obtain ⟨hwin,hwwhole⟩ := actual_endpoint_bigon_intruding_arc_localization M
      (r uF) (rT u) (r w) (hd w uF hwuF) hwb f hf hboundaryImage hentry
    have hwnonloop : (r w).val.map (0 : Interval) ≠ (r w).val.map 1 := by
      intro hloop
      apply actual_essential_loop_not_in_interior_free_disk M (r w) hloop d hdisk hdmarks
      rw [hdimage]
      exact hwwhole
    have hcollision := actual_terminal_empty_bigon_contained_nonloop_arc_class
      (r uF) (r w) hwnonloop f hf A B p q hA hB hwhole haImage hpmark hqmark
      hboundary hfree hwwhole hwin
    have hclasses : u.val=w.val := (hr uF).symm.trans (hcollision.trans (hr w))
    apply hu
    rw [hclasses]
    exact hwJ

  have actual_terminal_prescribed_bigon_produces_graph_relative_alignment
      (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
      (r : {w // w ∈ F} → EssentialMarkedArc M)
      (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w)=w.val)
      (hd : ∀ w z, w≠z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
      (haligned : ∀ w : {w // w ∈ T.val}, w.val ∈ J → r ⟨w.val,hTF w.property⟩=rT w)
      (u : {w // w ∈ T.val}) (hu : u.val ∉ J)
      (f : Plane → S) (hf : Topology.IsOpenEmbedding f)
      (A B : Set Plane) (p q : Plane)
      (hA : IsArcBetween A p q) (hB : IsArcBetween B p q)
      (hwhole : A ∪ B=modelCurve)
      (haImage : (r ⟨u.val,hTF u.property⟩).val.image=f '' A)
      (hbImage : (rT u).val.image=f '' B)
      (hpmark : f p ∈ M.cover.branch) (hqmark : f q ∈ M.cover.branch)
      (hboundary : ∀ z ∈ modelCurve, f z ∈ M.cover.branch → z=p ∨ z=q)
      (hfree : ∀ z ∈ Plane.openSquare 0 1, f z ∉ M.cover.branch)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S))
      (hdisk : Topology.IsEmbedding d)
      (hdimage : Set.range d=f '' Plane.closedSquare 0 1)
      (hdmarks : Disjoint
        (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S)) :
      ∃ H : AmbientIsotopy S,
        (∀ t z, z ∈ M.cover.branch → H.map (t,z)=z) ∧
        (∀ t z, z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
        H.finalMap '' (r ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image := by
    letI : T2Space S := M.sphere.symm.t2Space
    have hclear := actual_terminal_prescribed_bigon_avoids_entire_aligned_graph
      F J hTF hJT r hr hd haligned u hu f hf A B p q hA hB hwhole haImage hbImage
      hpmark hqmark hboundary hfree d hdisk hdimage hdmarks
    have hAP := actual_next_arc_disjoint_support_graph M r hd J
      (⟨u.val,hTF u.property⟩ : {w // w ∈ F}) hu
    have hBP := actual_target_arc_disjoint_aligned_graph M J T.val F hJT hTF
      r rT hdT haligned u hu
    have hinside : ∀ z ∈ Plane.openSquare 0 1,
        f z ∉ M.cover.branch ∧ f z ∉ actualObjectTrace M r J := by
      intro z hz
      exact ⟨hfree z hz,fun hzg => Set.disjoint_left.mp hclear ⟨z,hz,rfl⟩ hzg⟩
    exact actual_endpoint_bigon_relative_alignment M (r ⟨u.val,hTF u.property⟩) (rT u)
      (actualObjectTrace M r J) (actualObjectTrace_compact M r J).isClosed hAP hBP
      f hf A B p q hA hB hwhole haImage hbImage hpmark hqmark hboundary hinside

  have hab : Quotient.mk (essentialArcSetoid M) (r0 ⟨u.val,hTF u.property⟩)=
      Quotient.mk (essentialArcSetoid M) (rT u) := (hr0 _).trans (hrT u).symm
  have hmarkedEnds (c : MarkedArc M) : c.image ∩ (M.cover.branch:Set S)={c.map 0,c.map 1} := by
    ext z
    constructor
    · rintro ⟨⟨t,rfl⟩,ht⟩
      rcases c.marked_only_at_ends t ht with rfl | rfl <;> simp
    · intro hz
      rcases hz with he | he
      · subst z
        exact ⟨Set.mem_range_self 0,c.start_marked⟩
      · rw [mem_singleton_iff] at he
        subst z
        exact ⟨Set.mem_range_self 1,c.end_marked⟩
  have hend := arcEndpoints_isotopy_invariant M (r0 ⟨u.val,hTF u.property⟩) (rT u) (Quotient.exact hab)
  change ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,(r0 ⟨u.val,hTF u.property⟩).val.map 1}:Finset S)=
    {(rT u).val.map 0,(rT u).val.map 1} at hend
  have hends : ({(r0 ⟨u.val,hTF u.property⟩).val.map 0,(r0 ⟨u.val,hTF u.property⟩).val.map 1}:Set S)=
      {(rT u).val.map 0,(rT u).val.map 1} := by
    have hh := congrArg (fun t : Finset S => (t:Set S)) hend
    simpa only [Finset.coe_insert,Finset.coe_singleton] using hh
  have hmarkedImages :
      (r0 ⟨u.val,hTF u.property⟩).val.image ∩ (M.cover.branch:Set S)=
      (rT u).val.image ∩ (M.cover.branch:Set S) := by
    rw [hmarkedEnds,hmarkedEnds]
    exact hends
  have hlooptype := actual_same_class_loop_closure_invariant M
    (r0 ⟨u.val,hTF u.property⟩) (rT u) hab
  let a := r0 ⟨u.val,hTF u.property⟩
  let b := rT u
  have ha : a.val.map 0≠a.val.map 1 := ha
  have hmeet : a.val.image ∩ b.val.image={a.val.map 0,a.val.map 1} := by
    ext z
    constructor
    · rintro ⟨hza,hzb⟩
      have hzm : z ∈ M.cover.branch := by
        by_contra hzm
        have hzCross : z ∈ ArcSurgery.crossings M a b :=
          ⟨⟨hza,hzm⟩,⟨hzb,hzm⟩⟩
        have hzero : ArcSurgery.crossings M a b=∅ := hzero
        exact False.elim (by simpa only [hzero,Set.mem_empty_iff_false] using hzCross)
      rw [←hmarkedEnds a.val]
      exact ⟨hza,hzm⟩
    · intro hz
      have hza : z ∈ a.val.image ∩ (M.cover.branch : Set S) :=
        hmarkedEnds a.val ▸ hz
      have hzb : z ∈ b.val.image ∩ (M.cover.branch : Set S) :=
        hmarkedImages ▸ hza
      exact ⟨hza.1,hzb.1⟩
  obtain ⟨d,hd,hdfree,hdbdy⟩ :=
    actual_same_class_parallel_nonloop_comparison_disk M a b hab ha hmeet
  obtain ⟨hu₀,hv₀,α,β,hα,hβ,hhom⟩ :=
    actual_same_class_unoriented_nonloop_path_homotopy M a b hab ha
  let first : C(Interval,S) := ⟨a.val.map,a.val.continuous⟩
  let second : C(Interval,S) :=
    ⟨fun t => (β t).val,continuous_subtype_val.comp β.continuous⟩
  have hsecond : range second=b.val.image := by
    rcases hβ with hβ | hβ
    · apply congrArg range; exact funext hβ
    · exact (congrArg range (funext hβ)).trans
        (unitInterval.symmHomeomorph.surjective.range_comp _)
  have hb : b.val.map 0≠b.val.map 1 := by
    intro hb
    exact ha (hlooptype.mpr hb)
  have hfirstEmb : IsEmbedding first := NonLoopArc.isEmbedding ⟨a.val,ha⟩
  have hsecondEmb : IsEmbedding second := by
    rcases hβ with hβ | hβ
    · have he : (second : Interval → S)=b.val.map := funext hβ
      rw [he]; exact NonLoopArc.isEmbedding ⟨b.val,hb⟩
    · have he : (second : Interval → S)=b.val.map ∘ unitInterval.symm := funext hβ
      rw [he]
      exact (NonLoopArc.isEmbedding ⟨b.val,hb⟩).comp unitInterval.symmHomeomorph.isEmbedding
  have hsecond0 : second 0=a.val.map 0 := congrArg Subtype.val β.source
  have hsecond1 : second 1=a.val.map 1 := congrArg Subtype.val β.target
  have hdsplit : range d=
      (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1}) ∪
      (d '' {x | x.val ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1}) := by
    ext z
    constructor
    · rintro ⟨x,rfl⟩
      have hx : ‖x.val‖≤1 := by
        simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
      rcases hx.lt_or_eq with hx | hx
      · exact Or.inl ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_ball,dist_zero_right] using hx,rfl⟩
      · exact Or.inr ⟨x,by simpa only [Set.mem_setOf_eq,Metric.mem_sphere,dist_zero_right] using hx,rfl⟩
    · rintro (⟨x,hx,rfl⟩ | ⟨x,hx,rfl⟩) <;> exact mem_range_self x
  have hdmarks : ∀ z ∈ range d,z ∈ M.cover.branch → z=a.val.map 0 ∨ z=a.val.map 1 := by
    intro z hz hzm
    rw [hdsplit] at hz
    rcases hz with hz | hz
    · exact False.elim (disjoint_left.mp hdfree hz hzm)
    · rw [hdbdy] at hz
      have hza : z ∈ a.val.image ∩ (M.cover.branch : Set S) := by
        rcases hz with hza | hzb
        · exact ⟨hza,hzm⟩
        · exact hmarkedImages.symm ▸ (show z ∈ b.val.image ∩
            (M.cover.branch : Set S) from ⟨hzb,hzm⟩)
      have hzEnds := hmarkedEnds a.val ▸ hza
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hzEnds
  let D : ActualMarkedTwoSideDisk M a b := {
    firstCorner := a.val.map 0
    secondCorner := a.val.map 1
    firstSide := first
    secondSide := second
    first_embedded := hfirstEmb
    second_embedded := hsecondEmb
    first_zero := rfl
    first_one := rfl
    second_zero := hsecond0
    second_one := hsecond1
    first_on_curve := fun z hz => hz
    second_on_curve := hsecond.le
    sides_inter := by rw [hsecond]; exact hmeet
    disk := d
    disk_embedded := hd
    boundary_eq := by rw [hsecond]; exact hdbdy
    marks_are_corners := by
      intro z hz hzm
      simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using hdmarks z hz hzm }
  obtain ⟨f,A,B,p₀,q₀,hf,hA,hB,hwhole,hfA,hfB,hfp,hfq,hfi⟩ :=
    actual_two_side_disk_produces_bigon_chart M a b D
  have hsq : Plane.closedSquare 0 1=Plane.openSquare 0 1 ∪ modelCurve := by
    ext x
    simp only [mem_closedSquare_zero_one,Set.mem_union,mem_openSquare_zero_one,
      modelCurve,Set.mem_setOf_eq]
    exact le_iff_lt_or_eq
  have hfC : f '' modelCurve=a.val.image ∪ b.val.image := by
    rw [←hwhole,image_union,hfA,hfB]
    change range first ∪ range second=_
    rw [hsecond]; rfl
  have hdimage : range d=f '' Plane.closedSquare 0 1 := by
    rw [hsq,image_union,hfi,hfC,hdsplit,hdbdy]
    rfl
  have hboundary : ∀ z ∈ modelCurve,f z ∈ M.cover.branch → z=p₀ ∨ z=q₀ := by
    intro z hz hzm
    have hzD : f z ∈ range d := by
      rw [hdimage]
      exact mem_image_of_mem f (modelCurve_subset_closedSquare hz)
    rcases hdmarks (f z) hzD hzm with he | he
    · exact Or.inl (hf.injective (he.trans hfp.symm))
    · exact Or.inr (hf.injective (he.trans hfq.symm))
  have hinside : ∀ z ∈ Plane.openSquare 0 1,f z ∉ M.cover.branch := by
    intro z hz
    apply disjoint_left.mp hdfree
    change f z ∈ D.openInterior
    rw [←hfi]
    exact mem_image_of_mem f hz
  have hterminalProduced : ∃ (f : Plane → S) (A B : Set Plane) (p q : Plane)
      (d : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S)),
      IsOpenEmbedding f ∧ IsArcBetween A p q ∧ IsArcBetween B p q ∧
      A ∪ B=modelCurve ∧ a.val.image=f '' A ∧ b.val.image=f '' B ∧
      f p ∈ M.cover.branch ∧ f q ∈ M.cover.branch ∧
      (∀ z ∈ modelCurve,f z ∈ M.cover.branch → z=p ∨ z=q) ∧
      (∀ z ∈ Plane.openSquare 0 1,f z ∉ M.cover.branch) ∧
      IsEmbedding d ∧ range d=f '' Plane.closedSquare 0 1 ∧
      Disjoint (d '' {x | x.val ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) 1})
        (M.cover.branch : Set S) := by
    refine ⟨f,A,B,p₀,q₀,d,hf,hA,hB,hwhole,?_,?_,?_,?_,hboundary,hinside,hd,hdimage,hdfree⟩
    · exact hfA.symm
    · exact (hfB.trans hsecond).symm
    · rw [hfp]; exact a.val.start_marked
    · rw [hfq]; exact a.val.end_marked
  obtain ⟨f,A,B,p₀,q₀,d,hf,hA,hB,hwhole,haImage,hbImage,hpmark,hqmark,
    hboundary,hfree,hdisk,hdimage,hdmarks⟩ := hterminalProduced
  obtain ⟨K,hmK,hPK,hfinalK⟩ := actual_terminal_prescribed_bigon_produces_graph_relative_alignment
    F J hTF hJT r0 hr0 hd0 haligned0 u hu f hf A B p₀ q₀ hA hB hwhole
    haImage hbImage hpmark hqmark hboundary hfree d hdisk hdimage hdmarks
  rw [hgraph] at hPK
  exact ⟨K,hmK,hPK,hfinalK⟩

#print axioms actual_original_zero_contact_nonloop_graph_relative_alignment_private
end CurveComplex.HyperellipticModel
