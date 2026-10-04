import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGraphRelativeAlignmentPrivate
import CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalLoopGraphRelativeAlignmentPrivate
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

open Lean Elab Term in
elab "checkedRLCompletedOriginalNonloopRelativeAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalNonloopGraphRelativeAlignmentPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_nonloop_graph_relative_alignment_private
  discard <| getConstInfo n
  return mkConst n
open Lean Elab Term in
elab "checkedRLCompletedOriginalLoopRelativeAlignment" : term => do
  let n := (Lean.Name.num `_private.CurveComplexGenusTwo.Topology.ActualRestrictedLinkCone.ActualOriginalLoopGraphRelativeAlignmentPrivate 0).append
    `CurveComplex.HyperellipticModel.actual_original_loop_graph_relative_alignment_private
  discard <| getConstInfo n
  return mkConst n

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

/-- The positive-stratum conclusion of Lemmas 9.15 and 10.8. The geometric
cone apex must be built from a good complementary face of the arc graph. -/
theorem actualRestrictedLink_cone (M : HyperellipticModel E S)
    (p : ℕ) (hp : 1 ≤ p) (T : ActualStratum M p) :
    ∃ v : EssentialArcClass M,
      ({v} : Finset (EssentialArcClass M)) ∈ actualRestrictedLink M T ∧
      ∀ τ : Finset (EssentialArcClass M),
        τ ∈ actualRestrictedLink M T →
          insert v τ ∈ actualRestrictedLink M T := by
  classical
  obtain ⟨rT, hrT, hdT⟩ := (show IsArcSimplex M T.val from T.property.1)
  have hne : T.val.Nonempty := Finset.card_pos.mp (by rw [T.property.2.1]; omega)
  obtain ⟨O, U, hO, hOU, hUG, hfree, hlo, hhi⟩ :=
    actual_good_free_gap M rT hrT hdT T.property.2.2 hne
  obtain ⟨C, hC, f, hf, heU, x, hx, hxB⟩ :=
    actual_object_gap_marked_inside_chart M rT hrT hdT T.property.2.2 O hO U hOU
  have align_first_support_vertex (τ : Finset (EssentialArcClass M))
      (hτ : τ∈actualRestrictedLink M T) (u : {w // w∈T.val}) :
      ∃ r : {w // w∈T.val ∪ τ} → EssentialMarkedArc M,
        (∀ w,Quotient.mk (essentialArcSetoid M) (r w)=w.val) ∧
        (∀ w z,w≠z → Disjoint (arcInterior M (r w)) (arcInterior M (r z))) ∧
        r ⟨u.val,Finset.mem_union_left _ u.property⟩=rT u := by
    let uF : {w // w∈T.val ∪ τ} := ⟨u.val,Finset.mem_union_left _ u.property⟩
    obtain ⟨s,hs,hd⟩ := (show IsArcSimplex M (T.val ∪ τ) from hτ.2.1)
    have hab : Quotient.mk (essentialArcSetoid M) (s uF)=
        Quotient.mk (essentialArcSetoid M) (rT u) := (hs uF).trans (hrT u).symm
    obtain ⟨H,hm,hfinal⟩ := (Quotient.exact hab :
      MarkedIsotopyRel M (s uF).val.image (rT u).val.image)
    obtain ⟨r,hr,himage,hrdis,hkeep⟩ := actual_marked_family_transport_fixing_graph M s hd H hm
      (∅ : Set S) (fun _ _ hz => False.elim hz)
    have hclasses (w) : Quotient.mk (essentialArcSetoid M) (r w)=w.val := (hr w).trans (hs w)
    let J : Finset (EssentialArcClass M) := {u.val}
    have hJF : J ⊆ T.val ∪ τ := by
      intro w hw
      have he : w=u.val := Finset.mem_singleton.mp hw
      exact he.symm ▸ uF.property
    let rJ : {w // w∈J} → EssentialMarkedArc M := fun _ => rT u
    have hrJ (w : {w // w∈J}) : Quotient.mk (essentialArcSetoid M) (rJ w)=w.val :=
      (hrT u).trans (Finset.mem_singleton.mp w.property).symm
    have himages (w : {w // w∈J}) : (r ⟨w.val,hJF w.property⟩).val.image=(rJ w).val.image := by
      have hi : (⟨w.val,hJF w.property⟩ : {w // w∈T.val ∪ τ})=uF :=
        Subtype.ext (Finset.mem_singleton.mp w.property)
      rw [hi]
      exact (himage uF).trans hfinal
    obtain ⟨r',hr',hd',hrestrict,hwhole⟩ := actual_family_literal_restriction_of_aligned_images M
      J (T.val ∪ τ) hJF r hclasses hrdis rJ hrJ himages
    exact ⟨r',hr',hd',hrestrict ⟨u.val,Finset.mem_singleton_self _⟩⟩

  -- Consume an actual relative move and retain literal parametrizations on the enlarged support.
  have align_actual_relative_move
      (F J : Finset (EssentialArcClass M)) (hTF : T.val ⊆ F) (hJT : J ⊆ T.val)
      (u : {w // w ∈ T.val})
      (r : {w // w ∈ F} → EssentialMarkedArc M)
      (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val)
      (hd : ∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
      (haligned : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
        r ⟨w.val, hTF w.property⟩ = rT w)
      (H : AmbientIsotopy S)
      (hm : ∀ t z, z ∈ M.cover.branch → H.map (t,z)=z)
      (hP : ∀ t z, z ∈ actualObjectTrace M r J → H.map (t,z)=z)
      (hmove : H.finalMap '' (r ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image) :
      ∃ r' : {w // w ∈ F} → EssentialMarkedArc M,
        (∀ w, Quotient.mk (essentialArcSetoid M) (r' w) = w.val) ∧
        (∀ w z, w ≠ z → Disjoint (arcInterior M (r' w)) (arcInterior M (r' z))) ∧
        (∀ w : {w // w ∈ T.val}, w.val ∈ insert u.val J →
          r' ⟨w.val,hTF w.property⟩ = rT w) ∧
        ∀ w, (r' w).val.image=H.finalMap '' (r w).val.image := by
    let uF : {w // w ∈ F} := ⟨u.val,hTF u.property⟩
    obtain ⟨s, hs, himage, hdisj, hpres⟩ :=
      actual_marked_family_transport_fixing_graph M r hd H hm (actualObjectTrace M r J) hP
    have hnew : (s uF).val.image = (rT u).val.image :=
      (himage uF).trans hmove
    have hold (w : {w // w ∈ F}) (hw : w.val ∈ J) :
        (s w).val.image = (r w).val.image := by
      apply hpres w
      intro z hz
      exact Set.mem_iUnion.mpr ⟨w, Set.mem_iUnion.mpr ⟨hw, hz⟩⟩
    let J' := insert u.val J
    have hJ'T.val : J' ⊆ T.val := Finset.insert_subset u.property hJT
    have hJ'F : J' ⊆ F := hJ'T.val.trans hTF
    let rJ : {w // w ∈ J'} → EssentialMarkedArc M :=
      fun w => rT ⟨w.val, hJ'T.val w.property⟩
    have hrJ : ∀ w, Quotient.mk (essentialArcSetoid M) (rJ w) = w.val :=
      fun w => hrT _
    have himages : ∀ w : {w // w ∈ J'},
        (s ⟨w.val, hJ'F w.property⟩).val.image = (rJ w).val.image := by
      intro w
      rcases Finset.mem_insert.mp w.property with hwu | hwJ
      · have heF : (⟨w.val, hJ'F w.property⟩ : {w // w ∈ F}) = uF := Subtype.ext hwu
        have heT : (⟨w.val, hJ'T.val w.property⟩ : {w // w ∈ T.val}) = u := Subtype.ext hwu
        simpa only [rJ, heF, heT] using hnew
      · exact (hold _ hwJ).trans
          (congrArg (fun a : EssentialMarkedArc M => a.val.image)
            (haligned ⟨w.val, hJ'T.val w.property⟩ hwJ))
    obtain ⟨r', hr', hd', hrestrict, hkeep⟩ :=
      actual_family_literal_restriction_of_aligned_images M J' F hJ'F s
        (fun w => (hs w).trans (hr w)) hdisj rJ hrJ himages
    refine ⟨r', hr', hd', ?_, ?_⟩
    · intro w hw
      exact hrestrict ⟨w.val, hw⟩
    · intro w
      exact (hkeep w).trans (himage w)

  -- Original finite support alignment: owned source construction, not a new premise.
  have align (τ : Finset (EssentialArcClass M)) (hτ : τ ∈ actualRestrictedLink M T) :
      ∃ r : {w // w ∈ T.val ∪ τ} → EssentialMarkedArc M,
        (∀ w, Quotient.mk (essentialArcSetoid M) (r w) = w.val) ∧
        (∀ w z, w ≠ z → Disjoint (arcInterior M (r w)) (arcInterior M (r z))) ∧
        (∀ w, r ⟨w.val, Finset.mem_union_left _ w.property⟩ = rT w) := by
    by_cases hcard : T.val.card=1
    · obtain ⟨b,hTsingle⟩ := Finset.card_eq_one.mp hcard
      let u : {w // w∈T.val} := ⟨b,hTsingle.symm ▸ Finset.mem_singleton_self b⟩
      obtain ⟨r,hr,hd,hu⟩ := align_first_support_vertex τ hτ u
      refine ⟨r,hr,hd,?_⟩
      intro w
      have hwu : w=u := Subtype.ext (Finset.mem_singleton.mp (hTsingle ▸ w.property))
      subst w
      exact hu
    · have hTtwo : 2 ≤ T.val.card := by
        have hpos := Finset.card_pos.mpr hne
        omega
      let F := T.val ∪ τ
      have hTF : T.val ⊆ F := Finset.subset_union_left
      -- The remaining geometry is local to the NEXT actual arc, with the entire
      -- already aligned finite support graph preserved at every time.
      have moves (J : Finset (EssentialArcClass M)) (hJT : J ⊆ T.val)
          (r : {w // w ∈ F} → EssentialMarkedArc M)
          (hr : ∀ w, Quotient.mk (essentialArcSetoid M) (r w)=w.val)
          (hd : ∀ w z, w≠z → Disjoint (arcInterior M (r w)) (arcInterior M (r z)))
          (haligned : ∀ w : {w // w ∈ T.val}, w.val ∈ J →
            r ⟨w.val,hTF w.property⟩=rT w)
          (u : {w // w ∈ T.val}) (hu : u.val ∉ J) :
          ∃ H : AmbientIsotopy S,
            (∀ t z, z ∈ M.cover.branch → H.map (t,z)=z) ∧
            (∀ t z, z ∈ actualObjectTrace M r J → H.map (t,z)=z) ∧
            H.finalMap '' (r ⟨u.val,hTF u.property⟩).val.image=(rT u).val.image := by
        by_cases hloop : (r ⟨u.val,hTF u.property⟩).val.map 0=
            (r ⟨u.val,hTF u.property⟩).val.map 1
        · exact checkedRLCompletedOriginalLoopRelativeAlignment M p hp T F J hTF hJT
            r r hr hd rT hrT hdT haligned rfl u hu hloop
        · exact checkedRLCompletedOriginalNonloopRelativeAlignment M p T F J hTF hJT
            r r hr hd rT hrT hdT haligned rfl u hu hloop
      have build (J : Finset (EssentialArcClass M)) : J ⊆ T.val →
          ∃ r : {w // w ∈ F} → EssentialMarkedArc M,
            (∀ w, Quotient.mk (essentialArcSetoid M) (r w)=w.val) ∧
            (∀ w z, w≠z → Disjoint (arcInterior M (r w)) (arcInterior M (r z))) ∧
            (∀ w : {w // w ∈ T.val}, w.val ∈ J → r ⟨w.val,hTF w.property⟩=rT w) := by
        induction J using Finset.induction_on with
        | empty =>
          intro hJT
          obtain ⟨r,hr,hd⟩ := (show IsArcSimplex M F from hτ.2.1)
          exact ⟨r,hr,hd,fun w hw => False.elim (by simpa using hw)⟩
        | @insert a J ha ih =>
          intro hJT
          have haT : a ∈ T.val := hJT (Finset.mem_insert_self _ _)
          have hJsub : J ⊆ T.val := fun w hw => hJT (Finset.mem_insert_of_mem hw)
          obtain ⟨r,hr,hd,haligned⟩ := ih hJsub
          let u : {w // w ∈ T.val} := ⟨a,haT⟩
          obtain ⟨H,hm,hP,hmove⟩ := moves J hJsub r hr hd haligned u ha
          obtain ⟨r',hr',hd',haligned',himages⟩ :=
            align_actual_relative_move F J hTF hJsub u r hr hd haligned H hm hP hmove
          exact ⟨r',hr',hd',haligned'⟩
      obtain ⟨r,hr,hd,haligned⟩ := build T.val (fun _ hw => hw)
      exact ⟨r,hr,hd,fun w => haligned w w.property⟩
  let P := M.cover.branch.filter (fun z => z ∈ U)
  have hcard : P.card = 1 ∨ P.card = 2 := by dsimp [P]; omega
  rcases hcard with hcard | hcard
  · obtain ⟨b, hP⟩ := Finset.card_eq_one.mp hcard
    have hbP : b ∈ P := hP.symm ▸ Finset.mem_singleton_self b
    obtain ⟨hbB, hbU⟩ := Finset.mem_filter.mp hbP
    obtain ⟨q, hq, hqb⟩ := heU ▸ hbU
    have hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q := by
      intro z hz hzB
      have hmem : f z ∈ P := Finset.mem_filter.mpr ⟨hzB, heU.symm ▸ mem_image_of_mem f hz⟩
      rw [hP] at hmem
      exact hf.injective ((Finset.mem_singleton.mp hmem).trans hqb.symm)
    obtain ⟨a, ha0, ha1, haImage⟩ := actual_boundary_interior_mark_arc M f hf C hC x q
      hx hq hxB (hqb.symm ▸ hbB) hmarks
    have hane : a.val.map 0 ≠ a.val.map 1 := by
      rw [ha0, ha1]
      intro he
      exact inside_subset_compl hq (hf.injective he ▸ hx)
    have haIn : arcInterior M a ⊆ U := by
      intro z hz
      rcases haImage hz.1 with hzI | hzX
      · exact heU.symm ▸ hzI
      · exact False.elim (hz.2 ((Set.mem_singleton_iff.mp hzX).symm ▸ hxB))
    have haend : a.val.map 1 ∈ U := ha1.symm ▸ heU.symm ▸ mem_image_of_mem f hq
    refine ⟨Quotient.mk (essentialArcSetoid M) a,
      actual_gap_arc_link_vertex M T.val rT hrT hdT T.property.2.2 U hUG.2.2.1
        a hane haIn (Or.inr haend), ?_⟩
    intro τ hτ
    obtain ⟨r, hr, hd, hrestrict⟩ := align τ hτ
    exact actual_one_mark_aligned_restricted_link M p T τ hτ r hr hd rT hrestrict O hO
      U hOU hUG f hf C x q hC heU hx hq a ha0 ha1 haIn hmarks
  · obtain ⟨b, c, hbc, hP⟩ := Finset.card_eq_two.mp hcard
    have hbP : b ∈ P := hP.symm ▸ Finset.mem_insert_self b {c}
    have hcP : c ∈ P := hP.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self c)
    obtain ⟨hbB, hbU⟩ := Finset.mem_filter.mp hbP
    obtain ⟨hcB, hcU⟩ := Finset.mem_filter.mp hcP
    obtain ⟨q0, hq0, hq0b⟩ := heU ▸ hbU
    obtain ⟨q1, hq1, hq1c⟩ := heU ▸ hcU
    have hqne : q0 ≠ q1 := fun he => hbc (hq0b.symm.trans ((congrArg f he).trans hq1c))
    have hmarks : ∀ z ∈ inside C, f z ∈ M.cover.branch → z = q0 ∨ z = q1 := by
      intro z hz hzB
      have hmem : f z ∈ P := Finset.mem_filter.mpr ⟨hzB, heU.symm ▸ mem_image_of_mem f hz⟩
      rw [hP] at hmem
      rcases Finset.mem_insert.mp hmem with he | he
      · exact Or.inl (hf.injective (he.trans hq0b.symm))
      · exact Or.inr (hf.injective ((Finset.mem_singleton.mp he).trans hq1c.symm))
    obtain ⟨a, ha0, ha1, haImage⟩ := actual_two_mark_planar_apex M f hf C hC q0 q1
      hq0 hq1 hqne (hq0b.symm ▸ hbB) (hq1c.symm ▸ hcB) hmarks
    have haIn : a.val.image ⊆ U := heU.symm ▸ haImage
    have hane : a.val.map 0 ≠ a.val.map 1 := by
      rw [ha0, ha1]
      exact hf.injective.ne hqne
    have haend : a.val.map 0 ∈ U := ha0.symm ▸ heU.symm ▸ mem_image_of_mem f hq0
    refine ⟨Quotient.mk (essentialArcSetoid M) a,
      actual_gap_arc_link_vertex M T.val rT hrT hdT T.property.2.2 U hUG.2.2.1
        a hane (fun z hz => haIn hz.1) (Or.inl haend), ?_⟩
    intro τ hτ
    obtain ⟨r, hr, hd, hrestrict⟩ := align τ hτ
    exact actual_two_mark_aligned_restricted_link M p T τ hτ r hr hd rT hrestrict O hO
      U hOU hUG f hf C q0 q1 hC heU hq0 hq1 hqne a ha0 ha1 haIn hmarks
end CurveComplex.HyperellipticModel

#print axioms CurveComplex.HyperellipticModel.actualRestrictedLink_cone
