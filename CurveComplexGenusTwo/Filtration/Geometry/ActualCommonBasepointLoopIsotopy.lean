import CurveComplexGenusTwo.Filtration.Geometry.ActualEndpointBigonEnlargement
import CurveComplexGenusTwo.Topology.ArcCounts.ActualLowDegreeAssembly
import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import CurveComplexGenusTwo.Filtration.Geometry.ActualBigonMarkNamedHeader
import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
import CurveComplexGenusTwo.Topology.Smoothing.IncidentCircleRadialCoreStatement
import CurveComplexGenusTwo.Topology.Smoothing.PointedPlaneIsotopyProof
import CurveComplexGenusTwo.Topology.Smoothing.ConvexSectorChartHeader
import CurveComplexGenusTwo.Topology.Smoothing.JordanRegionIdentificationHeader
import CurveComplexGenusTwo.Topology.Smoothing.SeedMarkedArcDependency
import CurveComplexGenusTwo.Topology.Smoothing.JordanSectorCrosscutExtensionHeader
import CurveComplexGenusTwo.Topology.ArcStraightening
import CurveComplexGenusTwo.Topology.ChartLift
import CurveComplexGenusTwo.Topology.ArcCounts.ActualNumericDegree
import CurveComplexGenusTwo.Foundations.PlanarJordanNesting
import Schoenflies.SkeletonAccess
import Schoenflies.SkeletonLocal
import Schoenflies.RealizeSubdiv
import CurveComplexGenusTwo.Filtration.Geometry.NonloopPuncture
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import CurveComplexGenusTwo.Filtration.Geometry.ActualFaceMarksHeader
set_option maxHeartbeats 4000000
namespace CurveComplex.HyperellipticModel
open Set
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Two essential loops sharing only their common marked basepoint cannot
bound an unmarked full-graph face unless their actual marked isotopy classes
coincide. This is the figure-eight outside-region case, not the existing
nonloop Jordan-bigon theorem. -/
theorem actual_common_basepoint_loops_empty_face_class_equality
    (M : HyperellipticModel E S) (a b : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1)
    (hb : b.val.map 0 = b.val.map 1)
    (hbase : a.val.map 0 = b.val.map 0)
    (hmeet : a.val.image ∩ b.val.image = {a.val.map 0})
    (G U : Set S) (hG : IsClosed G)
    (haG : a.val.image ⊆ G) (hbG : b.val.image ⊆ G)
    (hU : IsComplementComponent G U)
    (hboundary : frontier U ⊆ a.val.image ∪ b.val.image)
    (hfree : ∀ z ∈ M.cover.branch, z ∉ U) :
    Quotient.mk (essentialArcSetoid M) a = Quotient.mk (essentialArcSetoid M) b := by
  classical
  letI : LocallyConnectedSpace S := actualSphere_locallyConnected M
  have hopen : IsOpen U := complementComponent_open hG hU
  have hUA : U ⊆ (a.val.image ∪ b.val.image)ᶜ := by
    intro x hx hxab
    rcases hxab with hxa | hxb
    · exact hU.2.2.1 hx (haG hxa)
    · exact hU.2.2.1 hx (hbG hxb)
  have hcomp : IsComplementComponent (a.val.image ∪ b.val.image) U := by
    refine ⟨hU.1, hU.2.1, hUA, ?_⟩
    intro V hV hUV hVA
    have hcl : closure U ∩ V ⊆ U := by
      intro x hx
      by_contra hn
      have hxf : x ∈ frontier U := by
        rw [hopen.frontier_eq]
        exact ⟨hx.1, hn⟩
      exact hVA hx.2 (hboundary hxf)
    have hVU : V ⊆ U := hV.isPreconnected.subset_of_closure_inter_subset hopen
      (by obtain ⟨x, hx⟩ := hU.1; exact ⟨x, hUV hx, hx⟩) hcl
    exact Set.Subset.antisymm hVU hUV
  obtain ⟨D⟩ := markedLoop_disc_decomposition_exists M a.val ha
  have hbconn : IsConnected (b.val.image \ {a.val.map 0}) := by
    rw [hbase]
    exact loop_image_remove_base_connected M b.val hb
  have hbsub : b.val.image \ {a.val.map 0} ⊆ a.val.imageᶜ := by
    intro x hx hxa
    have hxbase : x ∈ ({a.val.map 0} : Set S) := hmeet ▸ ⟨hxa, hx.1⟩
    exact hx.2 hxbase
  have hplace : ∃ i : Fin 2, b.val.image \ {a.val.map 0} ⊆ D.side i := by
    obtain ⟨x, hx⟩ := hbconn.nonempty
    let C := connectedComponentIn a.val.imageᶜ x
    have hC : IsComplementComponent a.val.image C :=
      complementComponent_iff_componentIn.mpr ⟨x, hbsub hx, rfl⟩
    obtain ⟨i, hi⟩ := (D.all_components C).mp hC
    refine ⟨i, ?_⟩
    rw [← hi]
    exact hbconn.isPreconnected.subset_connectedComponentIn hx hbsub
  have hUplace : ∃ j : Fin 2, U ⊆ D.side j := by
    obtain ⟨x, hx⟩ := hU.1
    have hxa : x ∈ a.val.imageᶜ := fun hm => hU.2.2.1 hx (haG hm)
    let C := connectedComponentIn a.val.imageᶜ x
    have hC : IsComplementComponent a.val.image C :=
      complementComponent_iff_componentIn.mpr ⟨x, hxa, rfl⟩
    obtain ⟨j, hj⟩ := (D.all_components C).mp hC
    refine ⟨j, ?_⟩
    rw [← hj]
    exact hU.2.1.isPreconnected.subset_connectedComponentIn hx
      (fun z hz hm => hU.2.2.1 hz (haG hm))
  obtain ⟨i, hi⟩ := hplace
  obtain ⟨j, hj⟩ := hUplace
  have hsameside : D.side i = D.side j := by
    by_contra hne
    have hdisj := complementComponents_disjoint (D.discs i).component
      (D.discs j).component hne
    have hsidefree : D.side j ⊆ (a.val.image ∪ b.val.image)ᶜ := by
      intro x hx hxab
      rcases hxab with hxa | hxb
      · exact (D.discs j).component.2.2.1 hx hxa
      · by_cases he : x = a.val.map 0
        · exact (D.discs j).component.2.2.1 hx
            (he ▸ Set.mem_range_self (0 : CurveComplex.Interval))
        · have hxin : x ∈ D.side i := hi ⟨hxb, by simpa using he⟩
          exact Set.disjoint_left.mp hdisj hxin hx
    have heq : D.side j = U := hcomp.2.2.2 _ (D.discs j).component.2.1 hj hsidefree
    have hmark : ∃ z, z ∈ M.cover.branch ∧ z ∈ D.side j := by
      rcases a.property with hnonloop | hregions
      · exact False.elim (hnonloop ha)
      · exact hregions _ (D.discs j).component
    obtain ⟨z, hz, hzj⟩ := hmark
    exact hfree z hz (heq ▸ hzj)
  have hUinside : U ⊆ D.side i := by rw [hsameside]; exact hj
  let k : Fin 2 := if i = 0 then 1 else 0
  have hik : D.side i ≠ D.side k := by
    fin_cases i
    · simpa [k] using D.distinct
    · simpa [k] using D.distinct.symm
  have hdiscs := complementComponents_disjoint (D.discs i).component (D.discs k).component hik
  have hothermark : ∃ p, p ∈ M.cover.branch ∧ p ∈ D.side k := by
    rcases a.property with hnonloop | hregions
    · exact False.elim (hnonloop ha)
    · exact hregions _ (D.discs k).component
  obtain ⟨puncture, hpuncture_mark, hpuncture_side⟩ := hothermark
  have hpuncture_a : puncture ∉ a.val.image := (D.discs k).component.2.2.1 hpuncture_side
  have hpuncture_base : puncture ≠ a.val.map 0 := by
    intro he
    exact hpuncture_a (he ▸ Set.mem_range_self (0 : CurveComplex.Interval))
  have hpuncture_b : puncture ∉ b.val.image := by
    intro hpB
    have hpI := hi ⟨hpB, by simpa using hpuncture_base⟩
    exact Set.disjoint_left.mp hdiscs hpI hpuncture_side
  have hpuncture_clU : puncture ∉ closure U := by
    intro hpcl
    have hpclI := closure_mono hUinside hpcl
    rw [(D.discs i).closure_eq] at hpclI
    rcases hpclI with hpI | hpA
    · exact Set.disjoint_left.mp hdiscs hpI hpuncture_side
    · exact hpuncture_a hpA
  have hfrontier_marks (z : S) (hz : z ∈ M.cover.branch) (hzf : z ∈ frontier U) :
      z = a.val.map 0 := by
    rcases hboundary hzf with hza | hzb
    · obtain ⟨t, rfl⟩ := hza
      rcases a.val.marked_only_at_ends t hz with ht | ht
      · exact congrArg a.val.map ht
      · rw [ht]
        exact ha.symm
    · obtain ⟨t, rfl⟩ := hzb
      rcases b.val.marked_only_at_ends t hz with ht | ht
      · rw [ht]
        exact hbase.symm
      · rw [ht]
        exact hb.symm.trans hbase.symm
  have hclosure_marks (z : S) (hz : z ∈ M.cover.branch) (hzcl : z ∈ closure U) :
      z = a.val.map 0 := by
    have hznot : z ∉ U := hfree z hz
    apply hfrontier_marks z hz
    rw [hopen.frontier_eq]
    exact ⟨hzcl, hznot⟩
  letI : T2Space S := M.sphere.symm.t2Space
  have loop_curve  {X : Type} [TopologicalSpace X] [T2Space X]
    (l : C(Interval, X)) (hend : l 0 = l 1)
    (hcoll : ∀ s t, l s = l t → s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) :
    ∃ c : Curve X, c.image = Set.range l := by
    let r := AddCircle.EndpointIdent (1 : ℝ) 0
    let j : Icc (0 : ℝ) (0 + 1) → Interval := fun t => ⟨t.val, by simpa using t.property⟩
    have hj : Continuous j := continuous_subtype_val.subtype_mk _
    have hrespect : ∀ a b, r a b → l (j a) = l (j b) := by
      rintro a b ⟨⟩
      simpa [j] using hend
    let L : Quot r → X := Quot.lift (fun t => l (j t)) hrespect
    have hL : Continuous L := continuous_quot_lift _ (l.continuous.comp hj)
    have hLi : Function.Injective L := by
      intro a b
      induction a using Quot.inductionOn with | h a =>
        induction b using Quot.inductionOn with | h b =>
          intro hab
          rcases hcoll (j a) (j b) hab with he | ⟨ha, hb⟩ | ⟨ha, hb⟩
          · apply congrArg (Quot.mk r)
            exact Subtype.ext (congrArg (fun t : Interval => t.val) he)
          · have ha' : a = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
            have hb' : b = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
            subst a; subst b
            exact Quot.sound AddCircle.EndpointIdent.mk
          · have ha' : a = ⟨0 + 1, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) ha)
            have hb' : b = ⟨0, by norm_num⟩ := Subtype.ext (by simpa [j] using congrArg (fun t : Interval => t.val) hb)
            subst a; subst b
            exact (Quot.sound AddCircle.EndpointIdent.mk).symm
    let e : Circle ≃ₜ Quot r :=
      (AddCircle.homeomorphCircle (T := (1 : ℝ)) one_ne_zero).symm.trans
        (AddCircle.homeoIccQuot (1 : ℝ) 0)
    let c : Curve X := ⟨L ∘ e, ((hL.comp e.continuous).isClosedEmbedding (hLi.comp e.injective)).isEmbedding⟩
    refine ⟨c, ?_⟩
    change range (L ∘ e) = range l
    rw [e.surjective.range_comp]
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      induction q using Quot.inductionOn with | h t =>
        exact ⟨j t, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Quot.mk r ⟨t.val, by simpa using t.property⟩, rfl⟩
  
  obtain ⟨ca, hca⟩ := loop_curve (⟨a.val.map, a.val.continuous⟩ : C(Interval, S)) ha a.val.injective_except_loop_closure
  obtain ⟨cb, hcb⟩ := loop_curve (⟨b.val.map, b.val.continuous⟩ : C(Interval, S)) hb b.val.injective_except_loop_closure
  have hca_image : ca.image = a.val.image := hca
  have hcb_image : cb.image = b.val.image := hcb
  let c : Bool → Curve S := fun j => if j then cb else ca
  have hcbase (j : Bool) : a.val.map 0 ∈ (c j).image := by
    cases j
    · change a.val.map 0 ∈ ca.image
      rw [hca_image]
      exact Set.mem_range_self (0 : CurveComplex.Interval)
    · change a.val.map 0 ∈ cb.image
      rw [hcb_image, hbase]
      exact Set.mem_range_self (0 : CurveComplex.Interval)
  have hcmeet (i j : Bool) (hne : i ≠ j) :
      (c i).image ∩ (c j).image = {a.val.map 0} := by
    cases i <;> cases j
    · exact False.elim (hne rfl)
    · simpa [c, hca_image, hcb_image] using hmeet
    · simpa [c, hca_image, hcb_image, Set.inter_comm] using hmeet
    · exact False.elim (hne rfl)
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  let e0 : OpenPartialHomeomorph S Schoenflies.Plane :=
    M.sphere.toOpenPartialHomeomorph.trans (stereographic' 2 (M.sphere puncture))
  have he0source : e0.source = {puncture}ᶜ := by
    ext x
    simp [e0, OpenPartialHomeomorph.trans_source]
  let e : OpenPartialHomeomorph S Schoenflies.Plane :=
    e0.trans (Homeomorph.addLeft (-e0 (a.val.map 0))).toOpenPartialHomeomorph
  have hesource : e.source = e0.source := by
    simp [e, OpenPartialHomeomorph.trans_source]
  have hebase : e (a.val.map 0) = 0 := by simp [e]
  let otherMarks : Finset S := M.cover.branch.erase (a.val.map 0)
  let N : Set S := e.source ∩ (otherMarks : Set S)ᶜ
  have hNopen : IsOpen N := e.open_source.inter otherMarks.isClosed.isOpen_compl
  have hbaseN : a.val.map 0 ∈ N := by
    constructor
    · rw [hesource, he0source]
      exact hpuncture_base.symm
    · simp [otherMarks]
  have hNsource : N ⊆ e.source := inter_subset_left
  have hNmeet (i j : Bool) (hne : i ≠ j) :
      N ∩ ((c i).image ∩ (c j).image) ⊆ {a.val.map 0} := by
    rw [hcmeet i j hne]
    exact inter_subset_right
  obtain ⟨ε, hεpos, hεpi, q, hq, R, hRopposite, hRcore⟩ :=
    CurveComplex.finite_incident_circle_radial_core c (a.val.map 0) hcbase
      e hebase N hNopen hbaseN hNsource hNmeet false
  letI : CompactSpace S := M.sphere.symm.compactSpace
  have hsupportTarget : Metric.closedBall (0 : Schoenflies.Plane) R.supportRadius ⊆ e.target := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := R.support_subset hz
    exact e.mapsTo (hNsource hx)
  obtain ⟨P, hPfinal, hPcenter, hPoutside⟩ :=
    supported_pointed_plane_isotopy 0 R.supportRadius R.support_pos R.H
      R.fixes_center R.fixes_exterior
  have hPclosed : ∀ t z, z ∉ Metric.closedBall (0 : Schoenflies.Plane) R.supportRadius →
      P.map (t, z) = z := by
    intro t z hz
    exact hPoutside t z (fun hh => hz (Metric.ball_subset_closedBall hh))
  obtain ⟨K, Gnorm, hcoord, hGU, hGoutside⟩ :=
    CurveComplex.position_surface_chart_lift S e.source e.target e.open_source
      e.toHomeomorphSourceTarget (Metric.closedBall (0 : Schoenflies.Plane) R.supportRadius)
      (isCompact_closedBall _ _) hsupportTarget P hPclosed
  have hcoord' (t : Interval) (x : e.source) :
      e (K.map (t, x)) = P.map (t, e x) := by
    simpa only [OpenPartialHomeomorph.toHomeomorphSourceTarget_apply_coe] using hcoord t x
  have hGpoint (t : Interval) (x : S) (hx : x ∈ e.source) :
      Gnorm.map (t, x) = e.symm (P.map (t, e x)) := by
    rw [hGU t ⟨x, hx⟩, ← hcoord' t ⟨x, hx⟩]
    exact (e.left_inv (K.map (t, ⟨x, hx⟩)).property).symm
  have hGoutN : ∀ t x, x ∉ N → Gnorm.map (t, x) = x := by
    intro t x hxN
    by_cases hx : x ∈ e.source
    · have hzout : e x ∉ Metric.closedBall (0 : Schoenflies.Plane) R.supportRadius := by
        intro hz
        obtain ⟨y, hy, he⟩ := R.support_subset hz
        have hyx : y = x := e.injOn (hNsource hy) hx he
        exact hxN (hyx ▸ hy)
      rw [hGpoint t x hx, hPclosed t (e x) hzout, e.left_inv hx]
    · exact hGoutside t x hx
  have hGcenter : ∀ t, Gnorm.map (t, a.val.map 0) = a.val.map 0 := by
    intro t
    rw [hGpoint t _ hbaseN.1, hebase, hPcenter, ← hebase, e.left_inv hbaseN.1]
  have hGmarks : ∀ t z, z ∈ M.cover.branch → Gnorm.map (t, z) = z := by
    intro t z hz
    by_cases he : z = a.val.map 0
    · subst z
      exact hGcenter t
    · apply hGoutN
      intro hzN
      exact hzN.2 (Finset.mem_erase.mpr ⟨he, hz⟩)
  have hnormA : MarkedIsotopyRel M a.val.image (Gnorm.finalMap '' a.val.image) :=
    ⟨Gnorm, hGmarks, rfl⟩
  have hnormB : MarkedIsotopyRel M b.val.image (Gnorm.finalMap '' b.val.image) :=
    ⟨Gnorm, hGmarks, rfl⟩
  let en : OpenPartialHomeomorph S Schoenflies.Plane :=
    e.trans R.H.toOpenPartialHomeomorph
  have hensource : en.source = e.source := by
    simp [en, OpenPartialHomeomorph.trans_source]
  have hentarget : en.target = Set.univ := by
    simp [en, e, e0, OpenPartialHomeomorph.trans_target]
  have henbase : en (a.val.map 0) = 0 := by
    change R.H (e (a.val.map 0)) = 0
    rw [hebase, R.fixes_center]
  have hsource_all (j : Bool) : (c j).image ⊆ en.source := by
    intro x hx
    rw [hensource, hesource, he0source]
    intro he
    have hxp : x = puncture := Set.mem_singleton_iff.mp he
    subst x
    cases j
    · exact hpuncture_a (by simpa [c, hca_image] using hx)
    · exact hpuncture_b (by simpa [c, hcb_image] using hx)
  let X : Bool → Set Schoenflies.Plane := fun j => en '' (c j).image
  have hlocalfan (j : Bool) (z : Schoenflies.Plane) (hz : ‖z‖ ≤ R.coreRadius) :
      z ∈ X j ↔ z ∈ segment ℝ 0 (R.vector (j, false)) ∪ segment ℝ 0 (R.vector (j, true)) := by
    constructor
    · rintro ⟨y, hy, hyz⟩
      have hyE : y ∈ e.source := hensource ▸ hsource_all j hy
      have hynorm : ‖R.H (e y)‖ ≤ R.coreRadius := by
        change ‖en y‖ ≤ R.coreRadius
        rw [hyz]
        exact hz
      have hfan := (hRcore j y hyE hynorm).mp hy
      change en y ∈ _ at hfan
      rwa [hyz] at hfan
    · intro hfan
      have hzt : z ∈ en.target := by rw [hentarget]; trivial
      let y := en.symm z
      have hyen : y ∈ en.source := en.mapsTo_symm hzt
      have hyE : y ∈ e.source := hensource ▸ hyen
      have hyz : en y = z := en.right_inv hzt
      have hynorm : ‖R.H (e y)‖ ≤ R.coreRadius := by
        change ‖en y‖ ≤ R.coreRadius
        rw [hyz]
        exact hz
      have hy : y ∈ (c j).image := (hRcore j y hyE hynorm).mpr (by
        change en y ∈ _
        rwa [hyz])
      exact ⟨y, hy, hyz⟩
  have fan_det {v z : Schoenflies.Plane} (hv : v ≠ 0)
      (hz : ‖z‖ < ‖v‖) :
      z ∈ segment ℝ 0 v ∪ segment ℝ 0 (-v) ↔ Schoenflies.Plane.det v z = 0 := by
    constructor
    · rintro (hz | hz)
      · obtain ⟨r, t, hr, ht, hrt, rfl⟩ := hz
        simp [Schoenflies.Plane.det]
        ring
      · obtain ⟨r, t, hr, ht, hrt, rfl⟩ := hz
        simp [Schoenflies.Plane.det]
        ring
    · intro he
      obtain ⟨r, rfl⟩ := (Schoenflies.Plane.det_eq_zero_iff_smul v z hv).mp he
      have hnorm : |r| * ‖v‖ < ‖v‖ := by simpa [norm_smul, Real.norm_eq_abs] using hz
      have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
      by_cases hr : 0 ≤ r
      · rw [abs_of_nonneg hr] at hnorm
        have hr1 : r ≤ 1 := by nlinarith
        exact Or.inl ⟨1-r, r, by linarith, hr, by ring, by module⟩
      · have hrneg : r < 0 := lt_of_not_ge hr
        rw [abs_of_neg hrneg] at hnorm
        have hr1 : -r ≤ 1 := by nlinarith
        exact Or.inr ⟨1+r, -r, by linarith, by linarith, by ring, by module⟩
  have hCJordan : Schoenflies.IsJordanCurve (X false) := by
    change Schoenflies.IsJordanCurve (en '' ca.image)
    rw [hca_image]
    change Schoenflies.IsJordanCurve (en '' Set.range a.val.map)
    rw [← Set.range_comp]
    exact markedLoop_chart_jordan M a.val ha en (fun t =>
      hsource_all false (by change a.val.map t ∈ ca.image; rw [hca_image]; exact Set.mem_range_self t))
  have hCbase : (0 : Schoenflies.Plane) ∈ X false :=
    ⟨a.val.map 0, hcbase false, henbase⟩
  have hCline (z : Schoenflies.Plane) (hz : z ∈ Metric.ball 0 R.coreRadius) :
      z ∈ X false ↔ Schoenflies.Plane.det (R.vector (false,false)) z = 0 := by
    have hzn : ‖z‖ < R.coreRadius := by simpa [Metric.mem_ball, dist_zero_right] using hz
    rw [hlocalfan false z hzn.le, hRopposite]
    exact fan_det (R.vector_nonzero _) (hzn.trans (R.core_lt_length _))
  let B0 : Set Schoenflies.Plane := en '' ((c true).image \ {a.val.map 0})
  have hB0conn : IsConnected B0 := by
    have hraw : IsConnected ((c true).image \ {a.val.map 0}) := by
      simpa [c, hcb_image] using hbconn
    exact hraw.image en (en.continuousOn.mono (fun x hx => hsource_all true hx.1))
  have hB0C : Disjoint B0 (X false) := by
    apply Set.disjoint_left.mpr
    rintro z ⟨x, hx, hxz⟩ ⟨y, hy, hyz⟩
    have hxy : x = y := en.injOn (hsource_all true hx.1) (hsource_all false hy)
      (hxz.trans hyz.symm)
    have hxa : x ∈ (c false).image := hxy.symm ▸ hy
    have hxbase : x = a.val.map 0 := by
      have hh : x ∈ (c false).image ∩ (c true).image := ⟨hxa, hx.1⟩
      rw [hcmeet false true (by decide)] at hh
      exact hh
    exact hx.2 (by simpa using hxbase)
  have jordan_local_halfplane {C B : Set Schoenflies.Plane} {v : Schoenflies.Plane} {ρ : ℝ}
      (hsep : Schoenflies.IsSeparating C) (hρ : 0 < ρ) (h0 : (0 : Schoenflies.Plane) ∈ C)
      (hlocal : ∀ x ∈ Metric.ball (0 : Schoenflies.Plane) ρ,
        x ∈ C ↔ Schoenflies.Plane.det v x = 0)
      (hB : IsConnected B) (hBC : Disjoint B C) :
      ∀ u ∈ B, ∀ w ∈ B, u ∈ Metric.ball (0 : Schoenflies.Plane) ρ →
        w ∈ Metric.ball (0 : Schoenflies.Plane) ρ →
        0 < Schoenflies.Plane.det v u * Schoenflies.Plane.det v w := by
    obtain ⟨T, V, hpair, hBT⟩ := hsep.exists_isRegionPair_subset hB.isPreconnected hB.nonempty hBC
    let L : Schoenflies.Plane →ₗ[ℝ] ℝ := {
      toFun := fun x => Schoenflies.Plane.det v x
      map_add' := Schoenflies.Plane.det_add_right v
      map_smul' := fun r x => Schoenflies.Plane.det_smul_right r v x }
    let Pos : Set Schoenflies.Plane := Metric.ball 0 ρ ∩ L ⁻¹' Set.Ioi 0
    let Neg : Set Schoenflies.Plane := Metric.ball 0 ρ ∩ L ⁻¹' Set.Iio 0
    have hPos : IsPreconnected Pos :=
      ((convex_ball (0 : Schoenflies.Plane) ρ).inter ((convex_Ioi (0 : ℝ)).linear_preimage L)).isPreconnected
    have hNeg : IsPreconnected Neg :=
      ((convex_ball (0 : Schoenflies.Plane) ρ).inter ((convex_Iio (0 : ℝ)).linear_preimage L)).isPreconnected
    have hPosC : Pos ⊆ Cᶜ := by
      intro x hx hxc
      have he := (hlocal x hx.1).mp hxc
      exact (ne_of_gt hx.2) he
    have hNegC : Neg ⊆ Cᶜ := by
      intro x hx hxc
      have he := (hlocal x hx.1).mp hxc
      exact (ne_of_lt hx.2) he
    have noOpp (u w : Schoenflies.Plane) (hu : u ∈ B) (hw : w ∈ B)
        (hub : u ∈ Metric.ball (0 : Schoenflies.Plane) ρ)
        (hwb : w ∈ Metric.ball (0 : Schoenflies.Plane) ρ)
        (hup : 0 < L u) (hwn : L w < 0) : False := by
      have hPosT : Pos ⊆ T := hPos.subset_left_of_subset_union
        (hpair.left.isOpen hsep) (hpair.right.isOpen hsep) hpair.disjoint
        (by rw [hpair.union_eq]; exact hPosC) ⟨u, ⟨hub, hup⟩, hBT hu⟩
      have hNegT : Neg ⊆ T := hNeg.subset_left_of_subset_union
        (hpair.left.isOpen hsep) (hpair.right.isOpen hsep) hpair.disjoint
        (by rw [hpair.union_eq]; exact hNegC) ⟨w, ⟨hwb, hwn⟩, hBT hw⟩
      have h0cl : (0 : Schoenflies.Plane) ∈ closure V := by
        apply frontier_subset_closure
        rw [hpair.right.frontier_eq hsep]
        exact h0
      obtain ⟨z, hzb, hzV⟩ := mem_closure_iff.mp h0cl (Metric.ball (0 : Schoenflies.Plane) ρ) Metric.isOpen_ball (by simpa using hρ)
      have hzC : z ∉ C := hpair.right.subset_compl hzV
      have hzL : L z ≠ 0 := fun he => hzC ((hlocal z hzb).mpr he)
      have hzT : z ∈ T := by
        rcases lt_or_gt_of_ne hzL with hn | hp
        · exact hNegT ⟨hzb, hn⟩
        · exact hPosT ⟨hzb, hp⟩
      exact Set.disjoint_left.mp hpair.disjoint hzT hzV
    intro u hu w hw hub hwb
    have huL : L u ≠ 0 := fun he => Set.disjoint_left.mp hBC hu ((hlocal u hub).mpr he)
    have hwL : L w ≠ 0 := fun he => Set.disjoint_left.mp hBC hw ((hlocal w hwb).mpr he)
    change 0 < L u * L w
    rcases lt_or_gt_of_ne huL with hun | hup
    · rcases lt_or_gt_of_ne hwL with hwn | hwp
      · exact mul_pos_of_neg_of_neg hun hwn
      · exact False.elim (noOpp w u hw hu hwb hub hwp hun)
    · rcases lt_or_gt_of_ne hwL with hwn | hwp
      · exact False.elim (noOpp u w hu hw hub hwb hup hwn)
      · exact mul_pos hup hwp
  have bent_crosscut {u w v : Schoenflies.Plane} {δ : ℝ}
      (hδ : 0 < δ) (hvu : 0 < Schoenflies.Plane.det v u)
      (hvw : 0 < Schoenflies.Plane.det v w)
      (huw : 0 < Schoenflies.Plane.det u w) :
      let q := δ • v
      let l := -q
      let B := (segment ℝ u q ∪ segment ℝ q l) ∪ segment ℝ l w
      Schoenflies.IsArcBetween B u w ∧ (0 : Schoenflies.Plane) ∈ B \ {u,w} ∧
        ∀ x ∈ B, Schoenflies.Plane.det v x = 0 ↔ x ∈ segment ℝ q l := by
    dsimp only
    let q := δ • v
    let l := -q
    have hl : l = (-δ) • v := by dsimp [l, q]; module
    have hvne : v ≠ 0 := by intro he; simp [he, Schoenflies.Plane.det] at hvu
    have hqne : q ≠ 0 := smul_ne_zero (ne_of_gt hδ) hvne
    have huq : u ≠ q := by
      intro he
      rw [he] at hvu
      simp [q] at hvu
    have hlw : l ≠ w := by
      intro he
      rw [← he] at hvw
      rw [hl] at hvw
      simp only [Schoenflies.Plane.det_smul_right, Schoenflies.Plane.det_self, mul_zero] at hvw
      linarith
    have hql : q ≠ l := by
      intro he
      have hh : q = -q := he
      have htwo : (2 : ℝ) • q = 0 := by
        calc
          (2 : ℝ) • q = q + q := by module
          _ = 0 := (congrArg (fun z => q + z) hh).trans (add_neg_cancel q)
      exact hqne ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
    have hcentral (x : Schoenflies.Plane) (hx : x ∈ segment ℝ q l) :
        Schoenflies.Plane.det v x = 0 := by
      obtain ⟨r, t, hr, ht, hrt, rfl⟩ := hx
      simp only [hl, q, Schoenflies.Plane.det_add_right, Schoenflies.Plane.det_smul_right,
        Schoenflies.Plane.det_self, mul_zero, add_zero]
    have hfirst (x : Schoenflies.Plane) (hx : x ∈ segment ℝ u q)
        (hz : Schoenflies.Plane.det v x = 0) : x = q := by
      obtain ⟨r, t, hr, ht, hrt, rfl⟩ := hx
      have he : r * Schoenflies.Plane.det v u = 0 := by
        simpa [q, Schoenflies.Plane.det_add_right] using hz
      have hr0 : r = 0 := (mul_eq_zero.mp he).resolve_right (ne_of_gt hvu)
      have ht1 : t = 1 := by linarith
      simp [hr0, ht1]
    have hlast (x : Schoenflies.Plane) (hx : x ∈ segment ℝ l w)
        (hz : Schoenflies.Plane.det v x = 0) : x = l := by
      obtain ⟨r, t, hr, ht, hrt, rfl⟩ := hx
      have he : t * Schoenflies.Plane.det v w = 0 := by
        simpa only [hl, Schoenflies.Plane.det_add_right, Schoenflies.Plane.det_smul_right,
          Schoenflies.Plane.det_self, mul_zero, zero_add] using hz
      have ht0 : t = 0 := (mul_eq_zero.mp he).resolve_right (ne_of_gt hvw)
      have hr1 : r = 1 := by linarith
      simp [ht0, hr1]
    have houter (x : Schoenflies.Plane) (hx : x ∈ segment ℝ u q)
        (hy : x ∈ segment ℝ l w) : False := by
      obtain ⟨r, t, hr, ht, hrt, hx⟩ := hx
      obtain ⟨s, k, hs, hk, hsk, hy⟩ := hy
      have he := congrArg (fun z => Schoenflies.Plane.det z w) (hx.trans hy.symm)
      simp only [Schoenflies.Plane.det_add_left, Schoenflies.Plane.det_smul_left,
        Schoenflies.Plane.det_self, mul_zero, add_zero] at he
      have hqdet : Schoenflies.Plane.det q w = δ * Schoenflies.Plane.det v w := by simp [q]
      have hldet : Schoenflies.Plane.det l w = -(δ * Schoenflies.Plane.det v w) := by
        rw [hl, Schoenflies.Plane.det_smul_left]
        ring
      rw [hqdet, hldet] at he
      have hL : 0 < δ * Schoenflies.Plane.det v w := mul_pos hδ hvw
      have hrD : 0 ≤ r * Schoenflies.Plane.det u w := mul_nonneg hr huw.le
      have htL : 0 ≤ t * (δ * Schoenflies.Plane.det v w) := mul_nonneg ht hL.le
      have hsL : 0 ≤ s * (δ * Schoenflies.Plane.det v w) := mul_nonneg hs hL.le
      have hrzero : r * Schoenflies.Plane.det u w = 0 := by linarith
      have htzero : t * (δ * Schoenflies.Plane.det v w) = 0 := by linarith
      have hr0 : r = 0 := (mul_eq_zero.mp hrzero).resolve_right (ne_of_gt huw)
      have ht0 : t = 0 := (mul_eq_zero.mp htzero).resolve_right (ne_of_gt hL)
      linarith
    have hA := (Schoenflies.isArcBetween_segment huq).concatenate
      (Schoenflies.isArcBetween_segment hql)
      (fun x hx hy => hfirst x hx (hcentral x hy))
    have hB : Schoenflies.IsArcBetween
        ((segment ℝ u q ∪ segment ℝ q l) ∪ segment ℝ l w) u w :=
      hA.concatenate (Schoenflies.isArcBetween_segment hlw) (by
        intro x hx hy
        rcases hx with hx | hx
        · exact False.elim (houter x hx hy)
        · exact hlast x hy (hcentral x hx))
    refine ⟨hB, ?_, ?_⟩
    · constructor
      · apply Or.inl
        apply Or.inr
        exact ⟨(1/2 : ℝ), (1/2 : ℝ), by norm_num, by norm_num, by norm_num, by change (1/2 : ℝ) • q + (1/2 : ℝ) • l = 0; dsimp [l]; module⟩
      · intro he
        rcases (show (0 : Schoenflies.Plane) = u ∨ 0 = w by simpa using he) with he | he
        · rw [← he] at hvu; simp [Schoenflies.Plane.det] at hvu
        · rw [← he] at hvw; simp [Schoenflies.Plane.det] at hvw
    · intro x hx
      constructor
      · intro hz
        rcases hx with (hx | hx) | hx
        · rw [hfirst x hx hz]
          exact left_mem_segment _ _ _
        · exact hx
        · rw [hlast x hx hz]
          exact right_mem_segment _ _ _
      · exact hcentral x
  let ρ : ℝ := R.coreRadius / 2
  have hρpos : 0 < ρ := half_pos R.core_pos
  have hρcore : ρ < R.coreRadius := by dsimp [ρ]; linarith [R.core_pos]
  let endpoint : Bool → Schoenflies.Plane := fun t =>
    (ρ / ‖R.vector (true,t)‖) • R.vector (true,t)
  have hcoef (t : Bool) : 0 < ρ / ‖R.vector (true,t)‖ ∧
      ρ / ‖R.vector (true,t)‖ < 1 := by
    have hvpos : 0 < ‖R.vector (true,t)‖ := norm_pos_iff.mpr (R.vector_nonzero _)
    exact ⟨div_pos hρpos hvpos, (div_lt_one hvpos).mpr (hρcore.trans (R.core_lt_length _))⟩
  have hendpointnorm (t : Bool) : ‖endpoint t‖ = ρ := by
    change ‖(ρ / ‖R.vector (true,t)‖) • R.vector (true,t)‖ = ρ
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hcoef t).1]
    exact div_mul_cancel₀ ρ (ne_of_gt (norm_pos_iff.mpr (R.vector_nonzero _)))
  have hendpointseg (t : Bool) : endpoint t ∈ segment ℝ 0 (R.vector (true,t)) := by
    refine ⟨1-ρ / ‖R.vector (true,t)‖, ρ / ‖R.vector (true,t)‖,
      by linarith [(hcoef t).2], (hcoef t).1.le, by ring, ?_⟩
    simp [endpoint]
  have hendpointne (t : Bool) : endpoint t ≠ 0 := by
    intro he
    have hh := hendpointnorm t
    rw [he, norm_zero] at hh
    linarith
  have hendpointX (t : Bool) : endpoint t ∈ X true := by
    apply (hlocalfan true (endpoint t) (by rw [hendpointnorm]; exact hρcore.le)).mpr
    cases t
    · exact Or.inl (hendpointseg false)
    · exact Or.inr (hendpointseg true)
  have hendpointB (t : Bool) : endpoint t ∈ B0 := by
    obtain ⟨y, hy, hye⟩ := hendpointX t
    refine ⟨y, ⟨hy, ?_⟩, hye⟩
    intro he
    have hybase : y = a.val.map 0 := he
    have hh : endpoint t = 0 := hye.symm.trans (hybase ▸ henbase)
    exact hendpointne t hh
  have hendpointball (t : Bool) : endpoint t ∈ Metric.ball 0 R.coreRadius := by
    simpa [Metric.mem_ball, dist_zero_right, hendpointnorm] using hρcore
  have hbSameHalf : 0 < Schoenflies.Plane.det (R.vector (false,false)) (endpoint false) *
      Schoenflies.Plane.det (R.vector (false,false)) (endpoint true) :=
    jordan_local_halfplane (Schoenflies.jordan_curve_theorem hCJordan) R.core_pos
      hCbase hCline hB0conn hB0C (endpoint false) (hendpointB false)
        (endpoint true) (hendpointB true) (hendpointball false) (hendpointball true)
  have hendpointdet : Schoenflies.Plane.det (endpoint false) (endpoint true) ≠ 0 := by
    intro he
    obtain ⟨t, ht⟩ := (Schoenflies.Plane.det_eq_zero_iff_smul
      (endpoint false) (endpoint true) (hendpointne false)).mp he
    have htnorm : |t| * ρ = ρ := by
      have hh := hendpointnorm true
      rw [ht, norm_smul, Real.norm_eq_abs, hendpointnorm false] at hh
      exact hh
    by_cases htpos : 0 ≤ t
    · rw [abs_of_nonneg htpos] at htnorm
      have ht1 : t = 1 := by nlinarith
      have heq : endpoint true = endpoint false := by simpa [ht1] using ht
      have hd := R.distinct_rays (true,false) (true,true) (by decide)
      simp only [zero_add] at hd
      apply Set.disjoint_left.mp hd
        (show endpoint false ∈ segment ℝ 0 (R.vector (true,false)) \ {0} from
          ⟨hendpointseg false, by simpa using hendpointne false⟩)
      exact ⟨heq ▸ hendpointseg true, by simpa using hendpointne false⟩
    · have htneg : t < 0 := lt_of_not_ge htpos
      rw [abs_of_neg htneg] at htnorm
      have htm : t = -1 := by nlinarith
      have heq : endpoint true = -endpoint false := by simpa [htm] using ht
      have hnegdet : Schoenflies.Plane.det (R.vector (false,false)) (endpoint true) =
          -Schoenflies.Plane.det (R.vector (false,false)) (endpoint false) := by
        rw [heq]
        simp [Schoenflies.Plane.det]
        ring
      rw [hnegdet] at hbSameHalf
      nlinarith [sq_nonneg (Schoenflies.Plane.det (R.vector (false,false)) (endpoint false))]
  let sourceCore : Set Schoenflies.Plane :=
    segment ℝ 0 (endpoint false) ∪ segment ℝ 0 (endpoint true)
  have hshortseg (t : Bool) : segment ℝ 0 (endpoint t) ⊆
      segment ℝ 0 (R.vector (true,t)) :=
    (convex_segment (0 : Schoenflies.Plane) (R.vector (true,t))).segment_subset
      (left_mem_segment ℝ 0 _) (hendpointseg t)
  have hsourceCore : Schoenflies.IsArcBetween sourceCore (endpoint false) (endpoint true) := by
    have hleft := Schoenflies.isArcBetween_segment (hendpointne false)
    have hright := Schoenflies.isArcBetween_segment (Ne.symm (hendpointne true))
    have hmeet : ∀ z ∈ segment ℝ (endpoint false) 0,
        z ∈ segment ℝ 0 (endpoint true) → z = 0 := by
      intro z hz hz'
      by_contra hne
      have hd := R.distinct_rays (true,false) (true,true) (by decide)
      simp only [zero_add] at hd
      exact Set.disjoint_left.mp hd
        ⟨hshortseg false (by simpa only [segment_symm] using hz), by simpa using hne⟩
        ⟨hshortseg true hz', by simpa using hne⟩
    simpa only [sourceCore, segment_symm] using hleft.concatenate hright hmeet
  have hsourceZero : (0 : Schoenflies.Plane) ∈ sourceCore \ {endpoint false, endpoint true} := by
    refine ⟨Or.inl (left_mem_segment ℝ _ _), ?_⟩
    simp only [mem_insert_iff, mem_singleton_iff, not_or]
    exact ⟨Ne.symm (hendpointne false), Ne.symm (hendpointne true)⟩
  have hradialcut (t : Bool) :
      segment ℝ 0 (R.vector (true,t)) ∩ Metric.closedBall 0 ρ =
        segment ℝ 0 (endpoint t) := by
    have hh := Schoenflies.segment_inter_closedBall (R.vector_nonzero (true,t)) hρpos
      (show ρ ≤ dist (0 : Schoenflies.Plane) (R.vector (true,t)) by
        rw [dist_zero_left]
        exact (hρcore.trans (R.core_lt_length _)).le)
    simpa only [endpoint, sub_zero, zero_add, Schoenflies.Plane.dir, smul_smul,
      div_eq_mul_inv] using hh
  have hsourceActual : X true ∩ Metric.closedBall 0 ρ = sourceCore := by
    ext z
    have hzsmall (hz : z ∈ Metric.closedBall (0 : Schoenflies.Plane) ρ) :
        ‖z‖ ≤ R.coreRadius := by
      have hh : ‖z‖ ≤ ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
      exact hh.trans hρcore.le
    constructor
    · rintro ⟨hzX,hzb⟩
      rcases (hlocalfan true z (hzsmall hzb)).mp hzX with hz | hz
      · exact Or.inl (hradialcut false ▸ (show z ∈ segment ℝ 0 (R.vector (true,false)) ∩
          Metric.closedBall 0 ρ from ⟨hz,hzb⟩))
      · exact Or.inr (hradialcut true ▸ (show z ∈ segment ℝ 0 (R.vector (true,true)) ∩
          Metric.closedBall 0 ρ from ⟨hz,hzb⟩))
    · intro hz
      have hcut : z ∈ (segment ℝ 0 (R.vector (true,false)) ∪
          segment ℝ 0 (R.vector (true,true))) ∩ Metric.closedBall 0 ρ := by
        rcases hz with hz | hz
        · have hh : z ∈ segment ℝ 0 (R.vector (true,false)) ∩ Metric.closedBall 0 ρ :=
            (hradialcut false).symm ▸ hz
          exact ⟨Or.inl hh.1,hh.2⟩
        · have hh : z ∈ segment ℝ 0 (R.vector (true,true)) ∩ Metric.closedBall 0 ρ :=
            (hradialcut true).symm ▸ hz
          exact ⟨Or.inr hh.1,hh.2⟩
      exact ⟨(hlocalfan true z (hzsmall hcut.2)).mpr hcut.1,hcut.2⟩
  obtain ⟨diskChart, hdiskInterior, hdiskClosed, hdiskFrontier, hdiskJordan⟩ :=
    convex_sector_ambient_square_chart (Metric.closedBall (0 : Schoenflies.Plane) ρ)
      (convex_closedBall _ _) Metric.isClosed_closedBall
      (by rw [interior_closedBall _ (ne_of_gt hρpos)]; exact ⟨0, Metric.mem_ball_self hρpos⟩)
      Metric.isBounded_closedBall
  have hdiskInside : Schoenflies.inside (frontier (Metric.closedBall (0 : Schoenflies.Plane) ρ)) =
      Metric.ball 0 ρ := by
    symm
    apply bounded_jordan_frontier_region_eq_inside hdiskJordan Metric.isOpen_ball
      ((convex_ball _ _).isConnected ⟨0, Metric.mem_ball_self hρpos⟩) Metric.isBounded_ball
    rw [frontier_ball _ (ne_of_gt hρpos), frontier_closedBall _ (ne_of_gt hρpos)]
  have hsourceBoundary (t : Bool) : endpoint t ∈
      frontier (Metric.closedBall (0 : Schoenflies.Plane) ρ) := by
    rw [frontier_closedBall _ (ne_of_gt hρpos)]
    simpa only [Metric.mem_sphere, dist_zero_right] using hendpointnorm t
  have hsourceInterior : sourceCore \ {endpoint false, endpoint true} ⊆
      Schoenflies.inside (frontier (Metric.closedBall (0 : Schoenflies.Plane) ρ)) := by
    rw [hdiskInside]
    rintro z ⟨hz, hzend⟩
    have hshortInside (t : Bool) (hz : z ∈ segment ℝ 0 (endpoint t)) :
        z ∈ Metric.ball (0 : Schoenflies.Plane) ρ := by
      obtain ⟨r,t',hr,ht,hrt,hz⟩ := hz
      have hz' : z = t' • endpoint t := by simpa using hz.symm
      have htl : t' < 1 := by
        have ht1 : t' ≤ 1 := by linarith
        by_contra hn
        have he : t' = 1 := le_antisymm ht1 (le_of_not_gt hn)
        have hzE : z = endpoint t := by simpa [he] using hz'
        apply hzend
        cases t <;> simp [hzE]
      rw [Metric.mem_ball, dist_zero_right, hz', norm_smul, Real.norm_eq_abs,
        abs_of_nonneg ht, hendpointnorm]
      nlinarith
    exact hz.elim (hshortInside false) (hshortInside true)
  have segment_boundary_interior {u q z : Schoenflies.Plane}
      (hu : ‖u‖ ≤ ρ) (hq : ‖q‖ < ρ)
      (hz : z ∈ segment ℝ u q) (hne : z ≠ u) : ‖z‖ < ρ := by
    obtain ⟨r,t,hr,ht,hrt,hz⟩ := hz
    have htp : 0 < t := by
      by_contra hn
      have ht0 : t = 0 := le_antisymm (le_of_not_gt hn) ht
      have hr1 : r = 1 := by linarith
      exact hne (by simpa [ht0,hr1] using hz.symm)
    have hnorm : ‖z‖ ≤ r * ‖u‖ + t * ‖q‖ := by
      rw [← hz]
      exact (norm_add_le _ _).trans (by
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg ht]
        exact le_rfl)
    have hru := mul_le_mul_of_nonneg_left hu hr
    have htq := mul_lt_mul_of_pos_left hq htp
    nlinarith
  have oriented_reference : ∃ v : Schoenflies.Plane,
      (v = R.vector (false,false) ∨ v = -R.vector (false,false)) ∧
      0 < Schoenflies.Plane.det v (endpoint false) ∧
      0 < Schoenflies.Plane.det v (endpoint true) := by
    have hn : Schoenflies.Plane.det (R.vector (false,false)) (endpoint false) ≠ 0 := by
      intro he
      rw [he,zero_mul] at hbSameHalf
      exact (lt_irrefl 0) hbSameHalf
    rcases lt_or_gt_of_ne hn with hneg | hpos
    · refine ⟨-R.vector (false,false), Or.inr rfl, ?_⟩
      have hneg' : Schoenflies.Plane.det (R.vector (false,false)) (endpoint true) < 0 := by
        nlinarith
      have hdet (z : Schoenflies.Plane) :
          Schoenflies.Plane.det (-R.vector (false,false)) z =
            -Schoenflies.Plane.det (R.vector (false,false)) z := by
        simp [Schoenflies.Plane.det]
        ring
      constructor <;> rw [hdet] <;> linarith
    · exact ⟨R.vector (false,false),Or.inl rfl,hpos,by nlinarith⟩
  have make_bend {u w v : Schoenflies.Plane}
      (hu : ‖u‖ = ρ) (hw : ‖w‖ = ρ)
      (hvu : 0 < Schoenflies.Plane.det v u)
      (hvw : 0 < Schoenflies.Plane.det v w)
      (huw : 0 < Schoenflies.Plane.det u w) :
      ∃ T : Set Schoenflies.Plane, Schoenflies.IsArcBetween T u w ∧
        (0 : Schoenflies.Plane) ∈ T \ {u,w} ∧
        T \ {u,w} ⊆ Metric.ball 0 ρ ∧
        ∃ q : Schoenflies.Plane, ‖q‖ = ρ / 2 ∧
          T ∩ {x | Schoenflies.Plane.det v x = 0} = segment ℝ q (-q) := by
    have hv : v ≠ 0 := by intro he; simp [he,Schoenflies.Plane.det] at hvu
    have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let δ : ℝ := ρ / (2 * ‖v‖)
    have hδ : 0 < δ := div_pos hρpos (mul_pos (by norm_num) hvnorm)
    let q : Schoenflies.Plane := δ • v
    let T : Set Schoenflies.Plane :=
      (segment ℝ u q ∪ segment ℝ q (-q)) ∪ segment ℝ (-q) w
    have hqn : ‖q‖ = ρ / 2 := by
      change ‖δ • v‖ = ρ / 2
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ]
      dsimp [δ]
      field_simp
    have hqi : q ∈ Metric.ball (0 : Schoenflies.Plane) ρ := by
      rw [Metric.mem_ball,dist_zero_right,hqn]
      linarith
    have hli : -q ∈ Metric.ball (0 : Schoenflies.Plane) ρ := by
      rw [Metric.mem_ball,dist_zero_right,norm_neg,hqn]
      linarith
    have hmain := bent_crosscut hδ hvu hvw huw
    change Schoenflies.IsArcBetween T u w ∧ (0 : Schoenflies.Plane) ∈ T \ {u,w} ∧
      ∀ x ∈ T, Schoenflies.Plane.det v x = 0 ↔ x ∈ segment ℝ q (-q) at hmain
    refine ⟨T,hmain.1,hmain.2.1,?_,q,hqn,?_⟩
    · rintro x ⟨hx,hxends⟩
      have hxu : x ≠ u := by intro he; apply hxends; simp [he]
      have hxw : x ≠ w := by intro he; apply hxends; simp [he]
      rcases hx with (hx | hx) | hx
      · have hh := segment_boundary_interior hu.le
          (show ‖q‖ < ρ by rw [hqn]; linarith) hx hxu
        simpa only [Metric.mem_ball,dist_zero_right] using hh
      · exact (convex_ball _ _).segment_subset hqi hli hx
      · have hh := segment_boundary_interior hw.le
          (show ‖-q‖ < ρ by rw [norm_neg,hqn]; linarith)
          (show x ∈ segment ℝ w (-q) by simpa only [segment_symm] using hx) hxw
        simpa only [Metric.mem_ball,dist_zero_right] using hh
    · ext x
      constructor
      · exact fun hx => (hmain.2.2 x hx.1).mp hx.2
      · intro hx
        have hxT : x ∈ T := Or.inl (Or.inr hx)
        exact ⟨hxT,(hmain.2.2 x hxT).mpr hx⟩
  have pointed_jordan_crosscut {C A B : Set Schoenflies.Plane} {a b p : Schoenflies.Plane}
      (hC : Schoenflies.IsJordanCurve C)
      (hA : Schoenflies.IsArcBetween A a b) (hB : Schoenflies.IsArcBetween B a b)
      (hpA : p ∈ A \ {a,b}) (hpB : p ∈ B \ {a,b})
      (ha : a ∈ C) (hb : b ∈ C)
      (hAi : A \ {a,b} ⊆ Schoenflies.inside C)
      (hBi : B \ {a,b} ⊆ Schoenflies.inside C) :
      ∃ F : Schoenflies.Plane ≃ₜ Schoenflies.Plane, F p = p ∧ F '' A = B ∧
        ∀ x, x ∉ Schoenflies.inside C → F x = x := by
    obtain ⟨e⟩ := Schoenflies.exists_arcHomeo hA hB
    have hpE : e.toFun p ∈ B \ {a,b} := by
      refine ⟨e.mapsTo hpA.1, ?_⟩
      intro hm
      have hcases : e.toFun p = a ∨ e.toFun p = b := by simpa using hm
      rcases hcases with he | he
      · have hpa : p = a := e.injOn hpA.1 hA.left_mem (he.trans e.map_left.symm)
        exact hpA.2 (by simp [hpa])
      · have hpb : p = b := e.injOn hpA.1 hA.right_mem (he.trans e.map_right.symm)
        exact hpA.2 (by simp [hpb])
    obtain ⟨g, hgp⟩ := CurveComplex.exists_marked_arcHomeo hB hpE hpB
    let h : Schoenflies.ArcHomeo A B a b a b := {
      toFun := g.toFun ∘ e.toFun
      invFun := e.invFun ∘ g.invFun
      continuousOn_toFun := g.continuousOn_toFun.comp e.continuousOn_toFun e.mapsTo
      continuousOn_invFun := e.continuousOn_invFun.comp g.continuousOn_invFun g.mapsTo_invFun
      leftInvOn := by
        intro x hx
        change e.invFun (g.invFun (g.toFun (e.toFun x))) = x
        rw [g.leftInvOn (e.mapsTo hx), e.leftInvOn hx]
      rightInvOn := by
        intro x hx
        change g.toFun (e.toFun (e.invFun (g.invFun x))) = x
        rw [e.rightInvOn (g.mapsTo_invFun hx), g.rightInvOn hx]
      image_eq := by rw [image_comp, e.image_eq, g.image_eq]
      map_left := by change g.toFun (e.toFun a) = a; rw [e.map_left,g.map_left]
      map_right := by change g.toFun (e.toFun b) = b; rw [e.map_right,g.map_right] }
    obtain ⟨F, hF, hFB, hfix⟩ :=
      jordan_sector_prescribed_crosscut_ambient_extension hC ha hb hA hB hAi hBi h
    refine ⟨F, ?_, hFB, hfix⟩
    exact (hF p hpA.1).trans hgp
  obtain ⟨v,hvref,hvleft,hvright⟩ := oriented_reference
  have hdetflip : Schoenflies.Plane.det (endpoint true) (endpoint false) =
      -Schoenflies.Plane.det (endpoint false) (endpoint true) := by
    simp [Schoenflies.Plane.det]
    ring
  have htargetCore : ∃ T : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween T (endpoint false) (endpoint true) ∧
      (0 : Schoenflies.Plane) ∈ T \ {endpoint false, endpoint true} ∧
      T \ {endpoint false, endpoint true} ⊆ Metric.ball 0 ρ ∧
      ∃ q : Schoenflies.Plane, ‖q‖ = ρ / 2 ∧
        T ∩ {x | Schoenflies.Plane.det v x = 0} = segment ℝ q (-q) := by
    rcases lt_or_gt_of_ne hendpointdet with hneg | hpos
    · obtain ⟨T,hT,h0T,hTi,q,hqn,hTline⟩ := make_bend (hendpointnorm true)
        (hendpointnorm false) hvright hvleft (by rw [hdetflip]; linarith)
      refine ⟨T,hT.reverse,?_,?_,q,hqn,hTline⟩
      · simpa only [Set.pair_comm] using h0T
      · simpa only [Set.pair_comm] using hTi
    · exact make_bend (hendpointnorm false) (hendpointnorm true) hvleft hvright hpos
  obtain ⟨targetCore,htargetArc,htargetZero,htargetInterior,qcore,hqcoreNorm,htargetLine⟩ := htargetCore
  obtain ⟨prefixHomeo,hprefixZero,hprefixImage,hprefixOutside⟩ := pointed_jordan_crosscut
    hdiskJordan hsourceCore htargetArc hsourceZero htargetZero
    (hsourceBoundary false) (hsourceBoundary true) hsourceInterior
    (by rw [hdiskInside]; exact htargetInterior)
  have hprefixFix : ∀ x, x ∉ Metric.ball (0 : Schoenflies.Plane) ρ → prefixHomeo x = x := by
    simpa only [hdiskInside] using hprefixOutside
  obtain ⟨prefixIsotopy,hprefixFinal,hprefixBase,hprefixExterior⟩ :=
    supported_pointed_plane_isotopy 0 ρ hρpos prefixHomeo hprefixZero hprefixFix
  have henmarks : ∀ z ∈ M.cover.branch, z ∈ en.source → z ≠ a.val.map 0 →
      en z ∉ Metric.closedBall (0 : Schoenflies.Plane) ρ := by
    intro z hz hzs hzne hball
    have ezout : e z ∉ Metric.closedBall (0 : Schoenflies.Plane) R.supportRadius := by
      intro he
      obtain ⟨y,hy,hye⟩ := R.support_subset he
      have hzy : z = y := e.injOn (hensource ▸ hzs) (hNsource hy) hye.symm
      exact hy.2 (Finset.mem_erase.mpr ⟨hzy ▸ hzne,hzy ▸ hz⟩)
    have ezoutball : e z ∉ Metric.ball (0 : Schoenflies.Plane) R.supportRadius :=
      fun hh => ezout (Metric.ball_subset_closedBall hh)
    have enz : en z = e z := R.fixes_exterior (e z) ezoutball
    rw [enz] at hball
    have hradii : ρ ≤ R.supportRadius := hρcore.le.trans R.core_lt_support.le
    exact ezout ((Metric.closedBall_subset_closedBall hradii) hball)
  have henTargetDisk : Metric.closedBall (0 : Schoenflies.Plane) ρ ⊆ en.target := by
    rw [hentarget]
    exact subset_univ _
  have hprefixClosed : ∀ t z, z ∉ Metric.closedBall (0 : Schoenflies.Plane) ρ →
      prefixIsotopy.map (t,z) = z := by
    intro t z hz
    exact hprefixExterior t z (fun hh => hz (Metric.ball_subset_closedBall hh))
  obtain ⟨prefixLift, prefixSurface, hprefixCoord, hprefixSurfaceCoord, hprefixSurfaceOutside⟩ :=
    CurveComplex.position_surface_chart_lift S en.source en.target en.open_source
      en.toHomeomorphSourceTarget (Metric.closedBall (0 : Schoenflies.Plane) ρ)
      (isCompact_closedBall _ _) henTargetDisk prefixIsotopy hprefixClosed
  have hprefixMarks : ∀ t z, z ∈ M.cover.branch → prefixSurface.map (t,z) = z := by
    intro t z hz
    by_cases hzs : z ∈ en.source
    · let zs : en.source := ⟨z,hzs⟩
      have hfix : prefixIsotopy.map (t,en z) = en z := by
        by_cases he : z = a.val.map 0
        · rw [he,henbase]
          exact hprefixBase t
        · exact hprefixClosed t (en z) (henmarks z hz hzs he)
      have hLift : prefixLift.map (t,zs) = zs := by
        apply en.toHomeomorphSourceTarget.injective
        apply Subtype.ext
        exact (hprefixCoord t zs).trans hfix
      exact (hprefixSurfaceCoord t zs).trans (congrArg Subtype.val hLift)
    · exact hprefixSurfaceOutside t z hzs
  have hprefixRel : MarkedIsotopyRel M b.val.image (prefixSurface.finalMap '' b.val.image) :=
    ⟨prefixSurface,hprefixMarks,rfl⟩
  have hprefixImageCoord : en '' (prefixSurface.finalMap '' b.val.image) =
      prefixHomeo '' X true := by
    have hbsource : b.val.image ⊆ en.source := by simpa [c,hcb_image] using hsource_all true
    have hcoordPoint (x : S) (hx : x ∈ en.source) :
        en (prefixSurface.finalMap x) = prefixHomeo (en x) := by
      let xs : en.source := ⟨x,hx⟩
      have hh := hprefixCoord (⟨1,by norm_num⟩ : Interval) xs
      change en (prefixLift.finalMap xs) = prefixIsotopy.finalMap (en x) at hh
      have hsurf := hprefixSurfaceCoord (⟨1,by norm_num⟩ : Interval) xs
      change prefixSurface.finalMap x = (prefixLift.finalMap xs : S) at hsurf
      rw [hsurf,hh,hprefixFinal]
    rw [Set.image_image]
    have hXb : X true = en '' b.val.image := by simp only [X,c,if_pos,hcb_image]
    rw [hXb]
    change (en ∘ prefixSurface.finalMap) '' b.val.image = prefixHomeo '' (en '' b.val.image)
    rw [Set.image_image]
    exact Set.image_congr (fun x hx => hcoordPoint x (hbsource hx))
  have hprefixBallInvariant (x : Schoenflies.Plane) :
      prefixHomeo x ∈ Metric.closedBall (0 : Schoenflies.Plane) ρ ↔
      x ∈ Metric.closedBall 0 ρ := by
    constructor
    · intro hh
      by_contra hx
      have hfix := hprefixFix x (fun hb => hx (Metric.ball_subset_closedBall hb))
      exact hx (hfix ▸ hh)
    · intro hx
      by_contra hh
      have hfix := hprefixFix (prefixHomeo x) (fun hb => hh (Metric.ball_subset_closedBall hb))
      have heq : prefixHomeo x = x := prefixHomeo.injective hfix
      exact hh (heq.symm ▸ hx)
  have hprefixActualCore : (prefixHomeo '' X true) ∩ Metric.closedBall 0 ρ = targetCore := by
    rw [← hprefixImage,← hsourceActual]
    ext z
    constructor
    · rintro ⟨⟨x,hx,rfl⟩,hzb⟩
      exact ⟨x,⟨hx,(hprefixBallInvariant x).mp hzb⟩,rfl⟩
    · rintro ⟨x,⟨hx,hxb⟩,rfl⟩
      exact ⟨⟨x,hx,rfl⟩,(hprefixBallInvariant x).mpr hxb⟩
  have hqcorePositive : 0 < ‖qcore‖ := by rw [hqcoreNorm]; linarith
  have hqcoreNe : qcore ≠ 0 := norm_pos_iff.mp hqcorePositive
  have hqcoreNegNe : qcore ≠ -qcore := by
    intro he
    have htwo : (2 : ℝ) • qcore = 0 := by
      calc
        (2 : ℝ) • qcore = qcore + qcore := by module
        _ = 0 := (congrArg (fun x => qcore + x) he).trans (add_neg_cancel qcore)
    exact hqcoreNe ((smul_eq_zero.mp htwo).resolve_left (by norm_num))
  have hqcoreBall : segment ℝ qcore (-qcore) ⊆ Metric.ball (0 : Schoenflies.Plane) ρ := by
    apply (convex_ball _ _).segment_subset
    · rw [Metric.mem_ball,dist_zero_right,hqcoreNorm]; linarith
    · rw [Metric.mem_ball,dist_zero_right,norm_neg,hqcoreNorm]; linarith
  have hqcoreTarget : segment ℝ qcore (-qcore) ⊆ targetCore := by
    intro z hz
    rw [← htargetLine] at hz
    exact hz.1
  have hvLine (z : Schoenflies.Plane) : Schoenflies.Plane.det v z = 0 ↔
      Schoenflies.Plane.det (R.vector (false,false)) z = 0 := by
    rcases hvref with he | he
    · rw [he]
    · rw [he]
      have hh : Schoenflies.Plane.det (-R.vector (false,false)) z =
          -Schoenflies.Plane.det (R.vector (false,false)) z := by
        simp [Schoenflies.Plane.det]
        ring
      rw [hh,neg_eq_zero]
  have hcentralInA : segment ℝ qcore (-qcore) ⊆ X false := by
    intro z hz
    have hzB := hqcoreBall hz
    have hzSmall : z ∈ Metric.ball (0 : Schoenflies.Plane) R.coreRadius :=
      (Metric.ball_subset_ball hρcore.le) hzB
    apply (hCline z hzSmall).mpr
    apply (hvLine z).mp
    exact (htargetLine ▸ hz).2
  have hcentralInB : segment ℝ qcore (-qcore) ⊆ prefixHomeo '' X true := by
    intro z hz
    have hzT := hqcoreTarget hz
    rw [← hprefixActualCore] at hzT
    exact hzT.1
  have hXmeet : X false ∩ X true = {(0 : Schoenflies.Plane)} := by
    ext z
    constructor
    · rintro ⟨⟨x,hx,hxz⟩,⟨y,hy,hyz⟩⟩
      have he : x = y := en.injOn (hsource_all false hx) (hsource_all true hy)
        (hxz.trans hyz.symm)
      have hxbase : x = a.val.map 0 := by
        apply Set.mem_singleton_iff.mp
        rw [← hcmeet false true (by decide)]
        exact ⟨hx,he.symm ▸ hy⟩
      exact Set.mem_singleton_iff.mpr (hxz.symm.trans (hxbase ▸ henbase))
    · intro hz
      have hz0 : z = 0 := Set.mem_singleton_iff.mp hz
      subst z
      exact ⟨⟨a.val.map 0,hcbase false,henbase⟩,⟨a.val.map 0,hcbase true,henbase⟩⟩
  have hprefixIntersection : X false ∩ (prefixHomeo '' X true) =
      segment ℝ qcore (-qcore) := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzA,hzB⟩
      by_cases hzb : z ∈ Metric.closedBall (0 : Schoenflies.Plane) ρ
      · have hzT : z ∈ targetCore := hprefixActualCore ▸ ⟨hzB,hzb⟩
        have hzSmall : z ∈ Metric.ball (0 : Schoenflies.Plane) R.coreRadius := by
          have hh : ‖z‖ ≤ ρ := by simpa only [Metric.mem_closedBall,dist_zero_right] using hzb
          simpa only [Metric.mem_ball,dist_zero_right] using hh.trans_lt hρcore
        have hzLine : Schoenflies.Plane.det v z = 0 := (hvLine z).mpr ((hCline z hzSmall).mp hzA)
        rw [← htargetLine]
        exact ⟨hzT,hzLine⟩
      · obtain ⟨x,hx,hxz⟩ := hzB
        have hfix : prefixHomeo z = z := hprefixFix z
          (fun hb => hzb (Metric.ball_subset_closedBall hb))
        have hxz' : x = z := prefixHomeo.injective (hxz.trans hfix.symm)
        have hz0 : z = 0 := Set.mem_singleton_iff.mp (hXmeet ▸ ⟨hzA,hxz' ▸ hx⟩)
        exact False.elim (hzb (hz0 ▸ Metric.mem_closedBall_self hρpos.le))
    · intro z hz
      exact ⟨hcentralInA hz,hcentralInB hz⟩
  have jordan_remove_subarc {C P : Set Schoenflies.Plane} {p q : Schoenflies.Plane}
      (hC : Schoenflies.IsJordanCurve C) (hP : Schoenflies.IsArcBetween P p q)
      (hPC : P ⊆ C) : ∃ A : Set Schoenflies.Plane,
      Schoenflies.IsArcBetween A p q ∧ P ∪ A = C ∧ P ∩ A = {p,q} := by
    obtain ⟨L,R,hcut⟩ := Schoenflies.exists_isCutPair hC
      (hPC hP.left_mem) (hPC hP.right_mem) hP.ne
    have hcover : P \ {p,q} ⊆ Rᶜ ∪ Lᶜ := by
      rintro x ⟨hx,hxe⟩
      by_cases hxR : x ∈ R
      · apply Or.inr
        intro hxL
        exact hxe (hcut.inter_eq ▸ ⟨hxL,hxR⟩)
      · exact Or.inl hxR
    have hdis : (P \ {p,q}) ∩ (Rᶜ ∩ Lᶜ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro x ⟨⟨hx,_⟩,hnR,hnL⟩
      have hh : x ∈ L ∪ R := hcut.union_eq.symm ▸ hPC hx
      exact hh.elim hnL hnR
    have hchoice := (isPreconnected_iff_subset_of_disjoint.mp hP.isPreconnected_diff)
      Rᶜ Lᶜ hcut.snd.isArc.isClosed.isOpen_compl hcut.fst.isArc.isClosed.isOpen_compl hcover hdis
    have hsubset {A B : Set Schoenflies.Plane} (hc : A ∪ B = C)
        (hnot : P \ {p,q} ⊆ Bᶜ) (hAcl : IsClosed A) : P ⊆ A := by
      have hdiff : P \ {p,q} ⊆ A := by
        intro x hx
        have hh : x ∈ A ∪ B := hc.symm ▸ hPC hx.1
        exact hh.resolve_right (hnot hx)
      rw [← hP.closure_diff_eq]
      exact closure_minimal hdiff hAcl
    rcases hchoice with hL | hR
    · have hpL : P ⊆ L := hsubset hcut.union_eq hL hcut.fst.isArc.isClosed
      have heq : P = L := hP.eq_of_subset_arc hcut.fst hcut.fst hpL (Subset.refl _)
      exact ⟨R,hcut.snd,heq.symm ▸ hcut.union_eq,heq.symm ▸ hcut.inter_eq⟩
    · have hpR : P ⊆ R := hsubset hcut.symm.union_eq hR hcut.snd.isArc.isClosed
      have heq : P = R := hP.eq_of_subset_arc hcut.snd hcut.snd hpR (Subset.refl _)
      exact ⟨L,hcut.fst,heq.symm ▸ hcut.symm.union_eq,heq.symm ▸ hcut.symm.inter_eq⟩
  have hBJordan : Schoenflies.IsJordanCurve (X true) := by
    change Schoenflies.IsJordanCurve (en '' cb.image)
    rw [hcb_image]
    change Schoenflies.IsJordanCurve (en '' Set.range b.val.map)
    rw [← Set.range_comp]
    exact markedLoop_chart_jordan M b.val hb en (fun t =>
      hsource_all true (by change b.val.map t ∈ cb.image; rw [hcb_image]; exact Set.mem_range_self t))
  have hBPrefixJordan : Schoenflies.IsJordanCurve (prefixHomeo '' X true) := by
    obtain ⟨f,hf,hfim⟩ := hBJordan
    refine ⟨prefixHomeo ∘ f, ?_, ?_⟩
    · refine ⟨prefixHomeo.continuous.comp_continuousOn hf.continuousOn, ?_, ?_⟩
      · exact congrArg prefixHomeo hf.closes
      · intro x hx y hy he
        exact hf.injOn hx hy (prefixHomeo.injective he)
    · rw [Set.image_comp,hfim]
  have hcentralArc := Schoenflies.isArcBetween_segment hqcoreNegNe
  obtain ⟨tailA,htailA,hcoverA,hmeetA⟩ := jordan_remove_subarc hCJordan hcentralArc hcentralInA
  obtain ⟨tailB,htailB,hcoverB,hmeetB⟩ := jordan_remove_subarc hBPrefixJordan hcentralArc hcentralInB
  have htailMeet : tailA ∩ tailB = {qcore,-qcore} := by
    apply Set.Subset.antisymm
    · rintro z ⟨hzA,hzB⟩
      have hzCA : z ∈ X false := hcoverA ▸ Or.inr hzA
      have hzCB : z ∈ prefixHomeo '' X true := hcoverB ▸ Or.inr hzB
      have hzCentral : z ∈ segment ℝ qcore (-qcore) := hprefixIntersection ▸ ⟨hzCA,hzCB⟩
      exact hmeetA ▸ ⟨hzCentral,hzA⟩
    · intro z hz
      rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hz : z = qcore ∨ z = -qcore) with rfl | rfl
      · exact ⟨htailA.left_mem,htailB.left_mem⟩
      · exact ⟨htailA.right_mem,htailB.right_mem⟩
  have htailJordan : Schoenflies.IsJordanCurve (tailA ∪ tailB) := by
    apply Schoenflies.isJordanCurve_union htailA htailB
    intro z hzA hzB
    have he : z ∈ ({qcore,-qcore} : Set Schoenflies.Plane) := htailMeet ▸ ⟨hzA,hzB⟩
    simpa only [mem_insert_iff,mem_singleton_iff] using he
  have hzeroCentral : (0 : Schoenflies.Plane) ∈ segment ℝ qcore (-qcore) := by
    refine ⟨(1/2 : ℝ),(1/2 : ℝ),by norm_num,by norm_num,by norm_num,?_⟩
    module
  have hzeroNotEnds : (0 : Schoenflies.Plane) ∉ ({qcore,-qcore} : Set Schoenflies.Plane) := by
    simp only [mem_insert_iff,mem_singleton_iff,not_or]
    exact ⟨Ne.symm hqcoreNe,by simpa using hqcoreNe⟩
  have hzeroNotTails : (0 : Schoenflies.Plane) ∉ tailA ∪ tailB := by
    intro hh
    rcases hh with hh | hh
    · exact hzeroNotEnds (hmeetA ▸ ⟨hzeroCentral,hh⟩)
    · exact hzeroNotEnds (hmeetB ▸ ⟨hzeroCentral,hh⟩)
  have hmarkTrace (j : Bool) (z : S) (hz : z ∈ M.cover.branch)
      (hzc : z ∈ (c j).image) : z = a.val.map 0 := by
    cases j
    · have hzA : z ∈ a.val.image := hca_image ▸ hzc
      obtain ⟨t,rfl⟩ := hzA
      rcases a.val.marked_only_at_ends t hz with ht | ht
      · exact congrArg a.val.map ht
      · rw [ht]; exact ha.symm
    · have hzB : z ∈ b.val.image := hcb_image ▸ hzc
      obtain ⟨t,rfl⟩ := hzB
      rcases b.val.marked_only_at_ends t hz with ht | ht
      · rw [ht]; exact hbase.symm
      · rw [ht]; exact hb.symm.trans hbase.symm
  have htailBoundaryUnmarked : ∀ z ∈ M.cover.branch, z ∈ en.source →
      en z ∉ tailA ∪ tailB := by
    intro z hz hzs hh
    have hz0 : en z = 0 := by
      rcases hh with hhA | hhB
      · have hzX : en z ∈ X false := hcoverA ▸ Or.inr hhA
        obtain ⟨x,hxc,hxz⟩ := hzX
        have hxz' : x = z := en.injOn (hsource_all false hxc) hzs hxz
        rw [← hxz'] at hz
        have hxbase := hmarkTrace false x hz hxc
        exact hxz.symm.trans (hxbase ▸ henbase)
      · have hzX : en z ∈ prefixHomeo '' X true := hcoverB ▸ Or.inr hhB
        have hfix : prefixHomeo (en z) = en z := by
          by_cases he : z = a.val.map 0
          · rw [he,henbase]; exact hprefixZero
          · exact hprefixFix _ (fun hb => henmarks z hz hzs he (Metric.ball_subset_closedBall hb))
        obtain ⟨x,⟨y,hy,hye⟩,hxz⟩ := hzX
        have hx : x = en z := prefixHomeo.injective (hxz.trans hfix.symm)
        have hyz : y = z := en.injOn (hsource_all true hy) hzs (hye.trans hx)
        have hybase := hmarkTrace true y (hyz.symm ▸ hz) hy
        exact (hye.trans hx).symm.trans (hybase ▸ henbase)
    exact hzeroNotTails (hz0 ▸ hh)
  have hsideClosureSource : closure (D.side i) ⊆ en.source := by
    intro z hz
    rw [hensource,hesource,he0source]
    intro he
    have hez : z = puncture := Set.mem_singleton_iff.mp he
    have hpcl : puncture ∈ closure (D.side i) := hez ▸ hz
    rw [(D.discs i).closure_eq] at hpcl
    exact hpcl.elim (fun hp => Set.disjoint_left.mp hdiscs hp hpuncture_side) hpuncture_a
  have hsideSource : D.side i ⊆ en.source := fun z hz => hsideClosureSource (subset_closure hz)
  let sidePlane : Set Schoenflies.Plane := en '' D.side i
  have hsideIsImage : en.IsImage (D.side i) sidePlane := by
    intro z hz
    constructor
    · rintro ⟨y,hy,hye⟩
      exact (en.injOn (hsideSource hy) hz hye) ▸ hy
    · exact fun hz => ⟨z,hz,rfl⟩
  have hsidePlaneOpen : IsOpen sidePlane := en.isOpen_image_of_subset_source
    (D.discs i).open_side hsideSource
  have hsidePlaneConn : IsConnected sidePlane := (D.discs i).component.2.1.image en
    (en.continuousOn.mono hsideSource)
  have hsidePlaneBounded : Bornology.IsBounded sidePlane := by
    have hc : IsCompact (closure (D.side i)) := isClosed_closure.isCompact
    have hci : IsCompact (en '' closure (D.side i)) := hc.image_of_continuousOn
      (en.continuousOn.mono hsideClosureSource)
    exact hci.isBounded.subset (Set.image_mono subset_closure)
  have hsidePlaneFrontier : frontier sidePlane = X false := by
    have heq := hsideIsImage.frontier.image_eq
    have hfrontSource : frontier (D.side i) ⊆ en.source :=
      fun z hz => hsideClosureSource (frontier_subset_closure hz)
    rw [Set.inter_eq_right.mpr hfrontSource,hentarget,Set.univ_inter,
      (D.discs i).boundary] at heq
    simpa only [X,c,if_neg Bool.false_ne_true,hca_image] using heq.symm
  have hsidePlaneInside : sidePlane = Schoenflies.inside (X false) :=
    bounded_jordan_frontier_region_eq_inside hCJordan hsidePlaneOpen hsidePlaneConn
      hsidePlaneBounded hsidePlaneFrontier
  have hBmiddleInside : X true \ {(0 : Schoenflies.Plane)} ⊆ Schoenflies.inside (X false) := by
    rintro z ⟨⟨x,hxc,hxz⟩,hzne⟩
    have hxcB : x ∈ b.val.image := hcb_image ▸ hxc
    have hxne : x ≠ a.val.map 0 := by
      intro he
      exact hzne (Set.mem_singleton_iff.mpr (hxz.symm.trans (he ▸ henbase)))
    rw [← hsidePlaneInside]
    exact ⟨x,hi ⟨hxcB,by simpa using hxne⟩,hxz⟩
  have hBclosedInside : X true ⊆ Schoenflies.inside (X false) ∪ X false := by
    intro z hz
    by_cases hz0 : z = 0
    · exact Or.inr (hz0 ▸ hCbase)
    · exact Or.inl (hBmiddleInside ⟨hz,by simpa using hz0⟩)
  have hBinsideA : Schoenflies.inside (X true) ⊆ Schoenflies.inside (X false) :=
    CurveComplex.jordan_inside_mono_of_boundary_subset_closed_inside
      (Schoenflies.jordan_curve_theorem hCJordan) (Schoenflies.jordan_curve_theorem hBJordan)
      hBclosedInside
  have hUclosureSource : closure U ⊆ en.source := by
    intro x hx
    rw [hensource,hesource,he0source]
    intro he
    exact hpuncture_clU ((Set.mem_singleton_iff.mp he) ▸ hx)
  have hUsource : U ⊆ en.source := fun x hx => hUclosureSource (subset_closure hx)
  let Uplane : Set Schoenflies.Plane := en '' U
  have hUimage : en.IsImage U Uplane := by
    intro x hx
    constructor
    · rintro ⟨y,hy,hye⟩
      exact en.injOn (hUsource hy) hx hye ▸ hy
    · exact fun hx => ⟨x,hx,rfl⟩
  have hUplaneOpen : IsOpen Uplane := en.isOpen_image_of_subset_source hopen hUsource
  have hUplaneConn : IsConnected Uplane := hU.2.1.image en (en.continuousOn.mono hUsource)
  have hUplaneInside : Uplane ⊆ Schoenflies.inside (X false) := by
    rw [← hsidePlaneInside]
    exact Set.image_mono hUinside
  have hUplaneB : Uplane ⊆ (X true)ᶜ := by
    rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
    have he : x = y := en.injOn (hUsource hx) (hsource_all true hy) (hxz.trans hyz.symm)
    have hyB : y ∈ b.val.image := hcb_image ▸ hy
    exact hUA hx (Or.inr (he.symm ▸ hyB))
  have hUplaneFrontier : frontier Uplane ⊆ X false ∪ X true := by
    have hf := hUimage.frontier.image_eq
    rw [Set.inter_eq_right.mpr (fun x hx => hUclosureSource (frontier_subset_closure hx)),
      hentarget,Set.univ_inter] at hf
    rw [← hf]
    rintro z ⟨x,hxf,hxz⟩
    rcases hboundary hxf with hxA | hxB
    · exact Or.inl ⟨x,by simpa only [c,if_neg Bool.false_ne_true,hca_image] using hxA,hxz⟩
    · exact Or.inr ⟨x,by simpa only [c,if_pos,hcb_image] using hxB,hxz⟩
  have hUplaneActual (z : Schoenflies.Plane) (hz : z ∈ Uplane) :
      connectedComponentIn (Schoenflies.inside (X false) \ X true) z = Uplane := by
    apply Schoenflies.Plane.connectedComponentIn_eq_of_frontier_disjoint hUplaneOpen
      hUplaneConn.isPreconnected
      (show Uplane ⊆ Schoenflies.inside (X false) \ X true from
        fun x hx => ⟨hUplaneInside hx,hUplaneB hx⟩) ?_ hz
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro x ⟨hxf,hxi,hxB⟩
    rcases hUplaneFrontier hxf with hxA | hxB'
    · exact Schoenflies.inside_subset_compl hxi hxA
    · exact hxB hxB'
  let bparam : ℝ → Schoenflies.Plane :=
    (en ∘ b.val.map) ∘ Set.projIcc 0 1 zero_le_one
  have hbparamCont : Continuous bparam :=
    (en.continuousOn.comp_continuous b.val.continuous (fun t =>
      hsource_all true (by change b.val.map t ∈ cb.image; rw [hcb_image]; exact Set.mem_range_self t))).comp
        continuous_projIcc
  have hbparamLoop : Schoenflies.IsLoop bparam := by
    refine ⟨hbparamCont.continuousOn,?_,?_⟩
    · simpa only [bparam,Function.comp_apply,Set.projIcc_of_mem zero_le_one
        Schoenflies.zero_mem_I,Set.projIcc_of_mem zero_le_one Schoenflies.one_mem_I]
        using congrArg en (show b.val.map ⟨0,Schoenflies.zero_mem_I⟩ =
          b.val.map ⟨1,Schoenflies.one_mem_I⟩ from hb)
    · intro t ht u hu he
      let ti : Interval := ⟨t,ht.1,ht.2.le⟩
      let ui : Interval := ⟨u,hu.1,hu.2.le⟩
      have heq : en (b.val.map ti) = en (b.val.map ui) := by
        simpa only [bparam,Function.comp_apply,Set.projIcc_of_mem zero_le_one ⟨ht.1,ht.2.le⟩,
          Set.projIcc_of_mem zero_le_one ⟨hu.1,hu.2.le⟩,ti,ui] using he
      have hbs (t : Interval) : b.val.map t ∈ en.source :=
        hsource_all true (by change b.val.map t ∈ cb.image; rw [hcb_image]; exact Set.mem_range_self t)
      rcases b.val.injective_except_loop_closure ti ui (en.injOn (hbs ti) (hbs ui) heq) with he | he | he
      · exact congrArg Subtype.val he
      · exact (hu.2.ne (congrArg Subtype.val he.2)).elim
      · exact (ht.2.ne (congrArg Subtype.val he.1)).elim
  have hbparamImage : bparam '' (Set.Icc (0 : ℝ) 1) = X true := by
    change bparam '' (Set.Icc (0 : ℝ) 1) = en '' cb.image
    rw [hcb_image]
    change bparam '' Set.Icc (0 : ℝ) 1 = en '' Set.range b.val.map
    rw [← Set.range_comp]
    ext z
    constructor
    · rintro ⟨t,ht,rfl⟩
      exact ⟨Set.projIcc 0 1 zero_le_one t,rfl⟩
    · rintro ⟨t,rfl⟩
      refine ⟨t,t.property,?_⟩
      simp [bparam,Function.comp_apply,Set.projIcc_of_mem]
  have hbparamBase : bparam 0 = 0 := by
    change en (b.val.map (Set.projIcc 0 1 zero_le_one 0)) = 0
    rw [Set.projIcc_of_mem zero_le_one Schoenflies.zero_mem_I]
    change en (b.val.map (0 : Interval)) = 0
    rw [← hbase,henbase]
  have hbparamMiddle : bparam '' Set.Ioo (0 : ℝ) 1 ⊆ Schoenflies.inside (X false) := by
    rintro z ⟨t,ht,rfl⟩
    apply hBmiddleInside
    refine ⟨hbparamImage ▸ (show bparam t ∈ bparam '' Set.Icc (0 : ℝ) 1 from
      ⟨t,⟨ht.1.le,ht.2.le⟩,rfl⟩),?_⟩
    intro he
    have heq : bparam t = bparam 0 := (Set.mem_singleton_iff.mp he).trans hbparamBase.symm
    exact (ne_of_gt ht.1) (hbparamLoop.injOn ⟨ht.1.le,ht.2⟩ ⟨le_rfl,zero_lt_one⟩ heq)
  obtain ⟨zL,hzL,zR,hzR,horiginalTwo⟩ := Schoenflies.actual_loop_domain_atMostTwo
    hbparamLoop (Schoenflies.jordan_curve_theorem hCJordan).isOpen_inside
    (Schoenflies.jordan_curve_theorem hCJordan).isConnected_inside.isPreconnected
    (by rw [hbparamBase]; exact fun he => Schoenflies.inside_subset_compl he hCbase)
    hbparamMiddle
  rw [hbparamImage] at hzL hzR horiginalTwo
  have hBinsideMarked : ∃ z ∈ M.cover.branch, z ∈ en.source ∧
      en z ∈ Schoenflies.inside (X true) := by
    let V : Set S := en.symm '' Schoenflies.inside (X true)
    have hinv : Topology.IsOpenEmbedding en.symm := en.symm.isOpenEmbedding hentarget
    have hVs : V ⊆ en.source := by
      rintro x ⟨y,hy,rfl⟩
      exact en.symm_mapsTo (hentarget ▸ Set.mem_univ y)
    have hVopen : IsOpen V := hinv.isOpenMap _
      (Schoenflies.jordan_curve_theorem hBJordan).isOpen_inside
    have hVconn : IsConnected V :=
      (Schoenflies.jordan_curve_theorem hBJordan).isConnected_inside.image en.symm hinv.continuous.continuousOn
    have hVimage : en.IsImage V (Schoenflies.inside (X true)) := by
      intro x hx
      constructor
      · intro he
        exact ⟨en x,he,en.left_inv hx⟩
      · rintro ⟨y,hy,hyx⟩
        rw [← hyx,en.right_inv (hentarget ▸ Set.mem_univ y)]
        exact hy
    have hcompactClosure : IsCompact (closure (Schoenflies.inside (X true))) :=
      Metric.isCompact_of_isClosed_isBounded isClosed_closure
        (Schoenflies.jordan_curve_theorem hBJordan).isBounded_inside.closure
    have hVclsource : closure V ⊆ en.source := by
      have hclosed : IsClosed (en.symm '' closure (Schoenflies.inside (X true))) :=
        (hcompactClosure.image hinv.continuous).isClosed
      have hclsub := closure_minimal (Set.image_mono (f := en.symm) subset_closure) hclosed
      rintro x hx
      obtain ⟨y,hy,rfl⟩ := hclsub hx
      exact en.symm_mapsTo (hentarget ▸ Set.mem_univ y)
    have hVfront : frontier V ⊆ b.val.image := by
      intro x hx
      have hxs := hVclsource (frontier_subset_closure hx)
      have hxf : en x ∈ frontier (Schoenflies.inside (X true)) :=
        (hVimage.frontier hxs).mpr hx
      rw [(Schoenflies.jordan_curve_theorem hBJordan).frontier_inside] at hxf
      obtain ⟨y,hy,hyx⟩ := hxf
      have hey : y = x := en.injOn (hsource_all true hy) hxs hyx
      exact hey ▸ (hcb_image ▸ hy)
    have hVsub : V ⊆ b.val.imageᶜ := by
      intro x hxV hxB
      have hxs := hVs hxV
      have hxin := (hVimage hxs).mpr hxV
      have hxXB : en x ∈ X true := ⟨x,hcb_image.symm ▸ hxB,rfl⟩
      exact Schoenflies.inside_subset_compl hxin hxXB
    have hVcomponent : IsComplementComponent b.val.image V := by
      refine ⟨hVconn.nonempty,hVconn,hVsub,?_⟩
      intro T hT hVT hTsub
      have hTV : T ⊆ V := hT.isPreconnected.subset_of_closure_inter_subset hVopen
        (by obtain ⟨x,hx⟩ := hVconn.nonempty; exact ⟨x,hVT hx,hx⟩) (by
          rintro x ⟨hxc,hxT⟩
          by_contra hxV
          have hxf : x ∈ frontier V := by rw [hVopen.frontier_eq]; exact ⟨hxc,hxV⟩
          exact hTsub hxT (hVfront hxf))
      exact Set.Subset.antisymm hTV hVT
    have hmark : ∃ z ∈ M.cover.branch, z ∈ V := by
      rcases b.property with hn | hs
      · exact False.elim (hn hb)
      · exact hs _ hVcomponent
    obtain ⟨z,hzm,hzV⟩ := hmark
    exact ⟨z,hzm,hVs hzV,(hVimage (hVs hzV)).mpr hzV⟩
  let originalCut : Set Schoenflies.Plane := Schoenflies.inside (X false) \ X true
  have hBinnerComponent (x : Schoenflies.Plane) (hx : x ∈ Schoenflies.inside (X true)) :
      connectedComponentIn originalCut x = Schoenflies.inside (X true) := by
    have hin := Schoenflies.jordan_curve_theorem hBJordan
    have hxcut : x ∈ originalCut := ⟨hBinsideA hx,Schoenflies.inside_subset_compl hx⟩
    apply Set.Subset.antisymm
    · have hs : connectedComponentIn originalCut x ⊆ connectedComponentIn (X true)ᶜ x :=
        (isConnected_connectedComponentIn_iff.mpr hxcut).isPreconnected.subset_connectedComponentIn
          (mem_connectedComponentIn hxcut) (fun z hz => (connectedComponentIn_subset _ _ hz).2)
      rwa [hin.connectedComponentIn_eq_inside hx] at hs
    · exact hin.isConnected_inside.isPreconnected.subset_connectedComponentIn hx
        (fun z hz => ⟨hBinsideA hz,Schoenflies.inside_subset_compl hz⟩)
  obtain ⟨innerMark,hinnerMark,hinnerSource,hinnerInside⟩ := hBinsideMarked
  obtain ⟨u,hu⟩ := hUplaneConn.nonempty
  have hinnerCut : en innerMark ∈ originalCut :=
    ⟨hBinsideA hinnerInside,Schoenflies.inside_subset_compl hinnerInside⟩
  have huCut : u ∈ originalCut := ⟨hUplaneInside hu,hUplaneB hu⟩
  have htwoDistinct : connectedComponentIn originalCut (en innerMark) ≠
      connectedComponentIn originalCut u := by
    intro he
    have hmarkU : en innerMark ∈ Uplane := by
      rw [← hUplaneActual u hu,← he]
      exact mem_connectedComponentIn hinnerCut
    have hmU : innerMark ∈ U := (hUimage hinnerSource).mp hmarkU
    exact hfree innerMark hinnerMark hmU
  have horiginalCover := Schoenflies.covered_by_two_components_of_ne horiginalTwo
    hinnerCut huCut htwoDistinct
  have hmarkedInsideEquivalence : ∀ z ∈ M.cover.branch, z ∈ en.source →
      (en z ∈ Schoenflies.inside (X false) ↔ en z ∈ Schoenflies.inside (X true)) := by
    intro z hz hzs
    constructor
    · intro hzA
      have hzBnot : en z ∉ X true := by
        intro he
        obtain ⟨y,hy,hye⟩ := he
        have hyz := en.injOn (hsource_all true hy) hzs hye
        have hzbase := hyz ▸ hmarkTrace true y (hyz.symm ▸ hz) hy
        have hz0 : en z = 0 := hzbase ▸ henbase
        exact Schoenflies.inside_subset_compl hzA (hz0 ▸ hCbase)
      rcases horiginalCover (en z) ⟨hzA,hzBnot⟩ with hzI | hzU
      · rw [hBinnerComponent (en innerMark) hinnerInside] at hzI
        exact hzI
      · rw [hUplaneActual u hu] at hzU
        exact False.elim (hfree z hz ((hUimage hzs).mp hzU))
    · exact fun hx => hBinsideA hx
  have hprefixInside : prefixHomeo '' Schoenflies.inside (X true) =
      Schoenflies.inside (prefixHomeo '' X true) := by
    have hbsep := Schoenflies.jordan_curve_theorem hBJordan
    have hc := Metric.isCompact_of_isClosed_isBounded isClosed_closure hbsep.isBounded_inside.closure
    apply bounded_jordan_frontier_region_eq_inside hBPrefixJordan
      (prefixHomeo.isOpenMap _ hbsep.isOpen_inside)
      (hbsep.isConnected_inside.image prefixHomeo prefixHomeo.continuous.continuousOn)
      ((hc.image prefixHomeo.continuous).isBounded.subset (Set.image_mono subset_closure))
    rw [← prefixHomeo.image_frontier,hbsep.frontier_inside]
  have hprefixMarkedInside : ∀ z ∈ M.cover.branch, z ∈ en.source →
      (en z ∈ Schoenflies.inside (X true) ↔
        en z ∈ Schoenflies.inside (prefixHomeo '' X true)) := by
    intro z hz hzs
    have hfix : prefixHomeo (en z) = en z := by
      by_cases he : z = a.val.map 0
      · rw [he,henbase]; exact hprefixZero
      · exact hprefixFix _ (fun hb => henmarks z hz hzs he (Metric.ball_subset_closedBall hb))
    rw [← hprefixInside]
    constructor
    · intro he
      exact ⟨en z,he,hfix⟩
    · rintro ⟨x,hx,hxe⟩
      have he : x = en z := prefixHomeo.injective (hxe.trans hfix.symm)
      exact he ▸ hx
  have hcoverARev : tailA ∪ segment ℝ qcore (-qcore) = X false := Set.union_comm _ _ |>.trans hcoverA
  have hcoverBRev : tailB ∪ segment ℝ qcore (-qcore) = prefixHomeo '' X true := Set.union_comm _ _ |>.trans hcoverB
  have htailCut : Schoenflies.IsCutPair (tailA ∪ tailB) qcore (-qcore) tailA tailB :=
    ⟨htailA,htailB,rfl,htailMeet⟩
  have hcentralFreeTail : segment ℝ qcore (-qcore) \ {qcore,-qcore} ⊆ (tailA ∪ tailB)ᶜ := by
    rintro z ⟨hz,hze⟩ hzt
    rcases hzt with hzt | hzt
    · exact hze (hmeetA ▸ ⟨hz,hzt⟩)
    · exact hze (hmeetB ▸ ⟨hz,hzt⟩)
  have hcentralOutside : segment ℝ qcore (-qcore) \ {qcore,-qcore} ⊆
      Schoenflies.outside (tailA ∪ tailB) := by
    obtain ⟨T,V,hpair,hPT⟩ := (Schoenflies.jordan_curve_theorem htailJordan).exists_isRegionPair_subset
      hcentralArc.isPreconnected_diff hcentralArc.nonempty_diff (Set.disjoint_left.mpr (fun x hx hc => hcentralFreeTail hx hc))
    rcases hpair with ⟨hTi,hVo⟩ | ⟨hTo,hVi⟩
    · have hPi : segment ℝ qcore (-qcore) \ {qcore,-qcore} ⊆ Schoenflies.inside (tailA ∪ tailB) :=
        hTi ▸ hPT
      have hclass := Schoenflies.general_crosscut_arbitrary_of_endpoints htailJordan hcentralArc htailCut hPi
      have hdis : Disjoint (Schoenflies.inside (X false))
          (Schoenflies.inside (prefixHomeo '' X true)) := by
        simpa only [hcoverARev,hcoverBRev] using hclass.2.1
      have hmA := hBinsideA hinnerInside
      have hmB := (hprefixMarkedInside innerMark hinnerMark hinnerSource).mp hinnerInside
      exact False.elim (Set.disjoint_left.mp hdis hmA hmB)
    · exact hTo ▸ hPT
  have htailInsideAvoidCentral : Schoenflies.inside (tailA ∪ tailB) ⊆
      (segment ℝ qcore (-qcore))ᶜ := by
    intro z hz hzP
    by_cases he : z ∈ ({qcore,-qcore} : Set Schoenflies.Plane)
    · have hzC : z ∈ tailA ∪ tailB := by
        rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using he : z=qcore ∨ z= -qcore) with rfl | rfl
        · exact Or.inl htailA.left_mem
        · exact Or.inl htailA.right_mem
      exact Schoenflies.inside_subset_compl hz hzC
    · exact Set.disjoint_left.mp Schoenflies.disjoint_inside_outside hz (hcentralOutside ⟨hzP,he⟩)
  have htailInsideAvoidLoops : Schoenflies.inside (tailA ∪ tailB) ⊆ (X false)ᶜ ∩
      (prefixHomeo '' X true)ᶜ := by
    intro z hz
    constructor
    · intro hzA
      rw [← hcoverA] at hzA
      exact hzA.elim (htailInsideAvoidCentral hz)
        (fun ht => Schoenflies.inside_subset_compl hz (Or.inl ht))
    · intro hzB
      rw [← hcoverB] at hzB
      exact hzB.elim (htailInsideAvoidCentral hz)
        (fun ht => Schoenflies.inside_subset_compl hz (Or.inr ht))
  have htailInsideUnmarked : ∀ z ∈ M.cover.branch, z ∈ en.source →
      en z ∉ Schoenflies.inside (tailA ∪ tailB) := by
    intro z hz hzs hzTail
    let C := tailA ∪ tailB
    let P := segment ℝ qcore (-qcore)
    have hCsep := Schoenflies.jordan_curve_theorem htailJordan
    have hAsep := Schoenflies.jordan_curve_theorem hCJordan
    have hBsep := Schoenflies.jordan_curve_theorem hBPrefixJordan
    have hAC : tailA ⊆ C := Set.subset_union_left
    have hBC : tailB ⊆ C := Set.subset_union_right
    have hPA : P ∩ C ⊆ tailA := by
      rintro x ⟨hxP,hxC⟩
      rcases hxC with hxA | hxB
      · exact hxA
      · have hxEnds : x ∈ ({qcore,-qcore} : Set Schoenflies.Plane) := hmeetB ▸ ⟨hxP,hxB⟩
        rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hxEnds : x=qcore ∨ x= -qcore) with rfl | rfl
        · exact htailA.left_mem
        · exact htailA.right_mem
    have hPB : P ∩ C ⊆ tailB := by
      rintro x ⟨hxP,hxC⟩
      rcases hxC with hxA | hxB
      · have hxEnds : x ∈ ({qcore,-qcore} : Set Schoenflies.Plane) := hmeetA ▸ ⟨hxP,hxA⟩
        rcases (by simpa only [mem_insert_iff,mem_singleton_iff] using hxEnds : x=qcore ∨ x= -qcore) with rfl | rfl
        · exact htailB.left_mem
        · exact htailB.right_mem
      · exact hxB
    have hneT : tailA ≠ tailB := by
      intro he
      have hp : tailA ⊆ ({qcore,-qcore} : Set Schoenflies.Plane) := by
        intro x hx
        exact htailMeet ▸ ⟨hx,he ▸ hx⟩
      exact htailA.not_subset_pair hp
    have hsepAP : Schoenflies.IsSeparating (tailA ∪ P) := by
      simpa only [P,hcoverARev] using hAsep
    have hsepBP : Schoenflies.IsSeparating (tailB ∪ P) := by
      simpa only [P,hcoverBRev] using hBsep
    have hΩ : Schoenflies.IsRegionPair C (Schoenflies.outside C) (Schoenflies.inside C) :=
      Or.inr ⟨rfl,rfl⟩
    have hsame : en z ∈ Schoenflies.inside (X false) ↔
        en z ∈ Schoenflies.inside (prefixHomeo '' X true) :=
      (hmarkedInsideEquivalence z hz hzs).trans (hprefixMarkedInside z hz hzs)
    have hsubregion (J : Set Schoenflies.Plane) (hJ : Schoenflies.IsSeparating J)
        (havoid : Schoenflies.inside C ⊆ Jᶜ) (W : Set Schoenflies.Plane)
        (hw : Schoenflies.IsRegionOf J W) (hzW : en z ∈ W) : Schoenflies.inside C ⊆ W := by
      have hs := hCsep.isConnected_inside.isPreconnected.subset_connectedComponentIn
        hzTail havoid
      have hc := hw.connectedComponentIn_eq hJ hzW
      rwa [hc] at hs
    by_cases hzA : en z ∈ Schoenflies.inside (X false)
    · have hzB := hsame.mp hzA
      have hsA := hsubregion (X false) hAsep (fun x hx => (htailInsideAvoidLoops hx).1)
        (Schoenflies.inside (X false)) (Schoenflies.IsRegionOf.inside _) hzA
      have hsB := hsubregion (prefixHomeo '' X true) hBsep (fun x hx => (htailInsideAvoidLoops hx).2)
        (Schoenflies.inside (prefixHomeo '' X true)) (Schoenflies.IsRegionOf.inside _) hzB
      have hpA : Schoenflies.IsRegionPair (tailA ∪ P)
          (Schoenflies.inside (X false)) (Schoenflies.outside (X false)) := by
        simpa only [P,hcoverARev] using
          (show Schoenflies.IsRegionPair (X false) (Schoenflies.inside (X false))
            (Schoenflies.outside (X false)) from Or.inl ⟨rfl,rfl⟩)
      have hpB : Schoenflies.IsRegionPair (tailB ∪ P)
          (Schoenflies.inside (prefixHomeo '' X true)) (Schoenflies.outside (prefixHomeo '' X true)) := by
        simpa only [P,hcoverBRev] using
          (show Schoenflies.IsRegionPair (prefixHomeo '' X true)
            (Schoenflies.inside (prefixHomeo '' X true))
            (Schoenflies.outside (prefixHomeo '' X true)) from Or.inl ⟨rfl,rfl⟩)
      have hc := Schoenflies.crosscut_cells hCsep hsepAP hsepBP hAC hBC hPA hPB hneT hΩ hpA hsA hpB hsB
      have hnsub : ¬Schoenflies.outside (X false) ⊆ closure (Schoenflies.inside (prefixHomeo '' X true)) := by
        intro hs
        exact hAsep.not_isBounded_outside (hBsep.isBounded_inside.closure.subset hs)
      obtain ⟨x,hxA,hxnot⟩ := Set.not_subset.mp hnsub
      have hxB : x ∈ Schoenflies.outside (prefixHomeo '' X true) := by
        have hxcurve : x ∉ prefixHomeo '' X true := by
          intro hh
          exact hxnot (frontier_subset_closure (hBsep.frontier_inside.symm ▸ hh))
        have hcover : x ∈ Schoenflies.inside (prefixHomeo '' X true) ∪
            Schoenflies.outside (prefixHomeo '' X true) := by
          rw [Schoenflies.inside_union_outside]; exact hxcurve
        exact hcover.resolve_left (fun hi => hxnot (subset_closure hi))
      exact hc.2.2.1 ((hc.1.2 x hxA).symm.trans (hc.2.1.2 x hxB))
    · have hzB : en z ∉ Schoenflies.inside (prefixHomeo '' X true) := fun he => hzA (hsame.mpr he)
      have hzAO : en z ∈ Schoenflies.outside (X false) := by
        have hcov : en z ∈ Schoenflies.inside (X false) ∪ Schoenflies.outside (X false) := by
          rw [Schoenflies.inside_union_outside]; exact (htailInsideAvoidLoops hzTail).1
        exact hcov.resolve_left hzA
      have hzBO : en z ∈ Schoenflies.outside (prefixHomeo '' X true) := by
        have hcov : en z ∈ Schoenflies.inside (prefixHomeo '' X true) ∪
            Schoenflies.outside (prefixHomeo '' X true) := by
          rw [Schoenflies.inside_union_outside]; exact (htailInsideAvoidLoops hzTail).2
        exact hcov.resolve_left hzB
      have hsA := hsubregion (X false) hAsep (fun x hx => (htailInsideAvoidLoops hx).1)
        (Schoenflies.outside (X false)) (Schoenflies.IsRegionOf.outside _) hzAO
      have hsB := hsubregion (prefixHomeo '' X true) hBsep (fun x hx => (htailInsideAvoidLoops hx).2)
        (Schoenflies.outside (prefixHomeo '' X true)) (Schoenflies.IsRegionOf.outside _) hzBO
      have hpA : Schoenflies.IsRegionPair (tailA ∪ P)
          (Schoenflies.outside (X false)) (Schoenflies.inside (X false)) := by
        simpa only [P,hcoverARev] using
          (show Schoenflies.IsRegionPair (X false) (Schoenflies.outside (X false))
            (Schoenflies.inside (X false)) from Or.inr ⟨rfl,rfl⟩)
      have hpB : Schoenflies.IsRegionPair (tailB ∪ P)
          (Schoenflies.outside (prefixHomeo '' X true)) (Schoenflies.inside (prefixHomeo '' X true)) := by
        simpa only [P,hcoverBRev] using
          (show Schoenflies.IsRegionPair (prefixHomeo '' X true)
            (Schoenflies.outside (prefixHomeo '' X true))
            (Schoenflies.inside (prefixHomeo '' X true)) from Or.inr ⟨rfl,rfl⟩)
      have hc := Schoenflies.crosscut_cells hCsep hsepAP hsepBP hAC hBC hPA hPB hneT hΩ hpA hsA hpB hsB
      have hmA := hBinsideA hinnerInside
      have hmB := (hprefixMarkedInside innerMark hinnerMark hinnerSource).mp hinnerInside
      exact hc.2.2.1 ((hc.1.2 (en innerMark) hmA).symm.trans (hc.2.1.2 (en innerMark) hmB))
  let markCoords : Finset Schoenflies.Plane := (M.cover.branch.filter (fun z => z ∈ en.source)).image en
  let obstacle : Set Schoenflies.Plane := segment ℝ qcore (-qcore) ∪ (markCoords : Set Schoenflies.Plane)
  have hobstacleClosed : IsClosed obstacle :=
    hcentralArc.isArc.isClosed.union markCoords.isClosed
  have hobstacleBoundary : ∀ z ∈ obstacle, z ∈ tailA ∪ tailB → z = qcore ∨ z = -qcore := by
    intro z hz hzTail
    rcases hz with hzP | hzM
    · have he : z ∈ ({qcore,-qcore} : Set Schoenflies.Plane) := by
        rcases hzTail with hzA | hzB
        · exact hmeetA ▸ ⟨hzP,hzA⟩
        · exact hmeetB ▸ ⟨hzP,hzB⟩
      simpa only [mem_insert_iff,mem_singleton_iff] using he
    · obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzM
      obtain ⟨hxm,hxs⟩ := Finset.mem_filter.mp hx
      exact False.elim (htailBoundaryUnmarked x hxm hxs (hxz.symm ▸ hzTail))
  have hobstacleInside : Disjoint (Schoenflies.inside (tailA ∪ tailB)) obstacle := by
    apply Set.disjoint_left.mpr
    intro z hzInside hzO
    rcases hzO with hzP | hzM
    · exact htailInsideAvoidCentral hzInside hzP
    · obtain ⟨x,hx,hxz⟩ := Finset.mem_image.mp hzM
      obtain ⟨hxm,hxs⟩ := Finset.mem_filter.mp hx
      exact htailInsideUnmarked x hxm hxs (hxz.symm ▸ hzInside)
  obtain ⟨boundaryChart⟩ := htailJordan.homeomorph_modelCurve
  obtain ⟨bigonChart,hbigonBoundary⟩ := Schoenflies.jordan_schoenflies_of_homeomorph
    htailJordan Schoenflies.isJordanCurve_modelCurve boundaryChart
  have hbigonCurve : bigonChart '' (tailA ∪ tailB) = Schoenflies.modelCurve := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      rw [hbigonBoundary ⟨x,hx⟩]
      exact (boundaryChart ⟨x,hx⟩).property
    · intro hz
      obtain ⟨x,hxz⟩ := boundaryChart.surjective ⟨z,hz⟩
      exact ⟨x,x.property,(hbigonBoundary x).trans (congrArg Subtype.val hxz)⟩
  have hbigonInside : bigonChart '' Schoenflies.inside (tailA ∪ tailB) =
      Schoenflies.Plane.openSquare 0 1 := by
    have hc := Schoenflies.jordan_curve_theorem htailJordan
    have hk := Metric.isCompact_of_isClosed_isBounded isClosed_closure hc.isBounded_inside.closure
    have hh : bigonChart '' Schoenflies.inside (tailA ∪ tailB) = Schoenflies.inside Schoenflies.modelCurve := by
      apply bounded_jordan_frontier_region_eq_inside Schoenflies.isJordanCurve_modelCurve
        (bigonChart.isOpenMap _ hc.isOpen_inside)
        (hc.isConnected_inside.image bigonChart bigonChart.continuous.continuousOn)
        ((hk.image bigonChart.continuous).isBounded.subset (Set.image_mono subset_closure))
      rw [← bigonChart.image_frontier,hc.frontier_inside,hbigonCurve]
    simpa only [Schoenflies.inside_modelCurve] using hh
  let normalObstacle : Set Schoenflies.Plane := bigonChart '' obstacle
  have hnormalClosed : IsClosed normalObstacle := bigonChart.isClosedMap _ hobstacleClosed
  have hnormalBoundary : ∀ z ∈ normalObstacle, z ∈ Schoenflies.modelCurve →
      z = bigonChart qcore ∨ z = bigonChart (-qcore) := by
    rintro z ⟨x,hx,hxz⟩ hzC
    rw [← hbigonCurve] at hzC
    obtain ⟨y,hy,hyz⟩ := hzC
    have hyx : y = x := bigonChart.injective (hyz.trans hxz.symm)
    rcases hobstacleBoundary x hx (hyx ▸ hy) with he | he
    · exact Or.inl (hxz.symm.trans (congrArg bigonChart he))
    · exact Or.inr (hxz.symm.trans (congrArg bigonChart he))
  have hnormalInside : Disjoint (Schoenflies.Plane.openSquare 0 1) normalObstacle := by
    apply Set.disjoint_left.mpr
    rintro z hz ⟨x,hx,hxz⟩
    rw [← hbigonInside] at hz
    obtain ⟨y,hy,hyz⟩ := hz
    have hyx : y = x := bigonChart.injective (hyz.trans hxz.symm)
    exact Set.disjoint_left.mp hobstacleInside (hyx ▸ hy) hx
  let normalA : Set Schoenflies.Plane := bigonChart '' tailA
  let normalB : Set Schoenflies.Plane := bigonChart '' tailB
  have hnormalA : Schoenflies.IsArcBetween normalA (bigonChart qcore) (bigonChart (-qcore)) :=
    htailA.image_of_injOn (Set.subset_univ _) bigonChart.continuous.continuousOn bigonChart.injective.injOn
  have hnormalB : Schoenflies.IsArcBetween normalB (bigonChart qcore) (bigonChart (-qcore)) :=
    htailB.image_of_injOn (Set.subset_univ _) bigonChart.continuous.continuousOn bigonChart.injective.injOn
  have hnormalWhole : normalA ∪ normalB = Schoenflies.modelCurve := by
    rw [← hbigonCurve,Set.image_union]
  obtain ⟨enlarge,henlargeP,henlargeQ,henlargeA,henlargeB,henlargeAi,henlargeBi,henlargeAvoid⟩ :=
    CurveComplex.actual_endpoint_preserving_bigon_enlargement normalA normalB
      (bigonChart qcore) (bigonChart (-qcore)) hnormalA hnormalB hnormalWhole
      normalObstacle hnormalClosed
      ⟨qcore,Or.inl (left_mem_segment ℝ _ _),rfl⟩
      ⟨-qcore,Or.inl (right_mem_segment ℝ _ _),rfl⟩ hnormalBoundary hnormalInside
  let replacementChart : Schoenflies.Plane ≃ₜ Schoenflies.Plane := bigonChart.trans enlarge.symm
  have hrepairA : enlarge.symm '' normalA = replacementChart '' tailA := by
    rw [← Set.image_comp]
    rfl
  have hrepairB : enlarge.symm '' normalB = replacementChart '' tailB := by
    rw [← Set.image_comp]
    rfl
  have hrepairAvoid : ∀ x ∈ obstacle, replacementChart x ∉ Schoenflies.Plane.openSquare 0 1 := by
    intro x hx hin
    have hf := henlargeAvoid (replacementChart x) hin
    apply hf
    refine ⟨x,hx,?_⟩
    exact (enlarge.apply_symm_apply (bigonChart x)).symm
  let er : OpenPartialHomeomorph S Schoenflies.Plane := en.trans replacementChart.toOpenPartialHomeomorph
  have hersource : er.source = en.source := by simp [er,OpenPartialHomeomorph.trans_source]
  have hertarget : er.target = Set.univ := by simp [er,OpenPartialHomeomorph.trans_target,hentarget]
  have hercoord (x : S) : er x = replacementChart (en x) := rfl
  have herSquare : Schoenflies.Plane.closedSquare 0 1 ⊆ er.target := by
    rw [hertarget]; exact subset_univ _
  have hnormalPcurve : bigonChart qcore ∈ Schoenflies.modelCurve := by
    rw [← hnormalWhole]; exact Or.inl hnormalA.left_mem
  have hnormalQcurve : bigonChart (-qcore) ∈ Schoenflies.modelCurve := by
    rw [← hnormalWhole]; exact Or.inl hnormalA.right_mem
  obtain ⟨tailSurface,htailSurfaceImage,htailSurfaceFix⟩ :=
    CurveComplex.position_crosscut_surface_square_support S er.source er.target er.open_source
      er.toHomeomorphSourceTarget herSquare
      (enlarge.symm '' normalB) (enlarge.symm '' normalA)
      (bigonChart qcore) (bigonChart (-qcore)) henlargeB henlargeA
      hnormalPcurve hnormalQcurve henlargeBi henlargeAi
  have hpullback (Q : Set Schoenflies.Plane) :
      {x : S | ∃ u : er.source, u.val = x ∧ (er.toHomeomorphSourceTarget u : Schoenflies.Plane) ∈
        replacementChart '' Q} = en.symm '' Q := by
    ext x
    constructor
    · rintro ⟨u,hux,q,hq,hqu⟩
      have hqen : q = en u := replacementChart.injective hqu
      refine ⟨q,hq,?_⟩
      rw [hqen,en.left_inv (hersource ▸ u.property),hux]
    · rintro ⟨q,hq,hqx⟩
      have hqs : en.symm q ∈ er.source := by
        rw [hersource]; exact en.symm_mapsTo (hentarget ▸ Set.mem_univ q)
      refine ⟨⟨en.symm q,hqs⟩,hqx,q,hq,?_⟩
      change replacementChart q = replacementChart (en (en.symm q))
      rw [en.right_inv (hentarget ▸ Set.mem_univ q)]
  rw [hrepairB,hrepairA,hpullback tailB,hpullback tailA] at htailSurfaceImage
  have htailMarks : ∀ t z, z ∈ M.cover.branch → tailSurface.map (t,z) = z := by
    intro t z hz
    apply htailSurfaceFix
    rintro ⟨u,huz,huSq⟩
    have hzs : z ∈ en.source := huz ▸ (hersource ▸ u.property)
    have hzO : en z ∈ obstacle := Or.inr (Finset.mem_image.mpr
      ⟨z,Finset.mem_filter.mpr ⟨hz,hzs⟩,rfl⟩)
    exact hrepairAvoid (en z) hzO (huz ▸ huSq)
  have htailCentral : ∀ t x, x ∈ en.symm '' segment ℝ qcore (-qcore) →
      tailSurface.map (t,x) = x := by
    intro t x hx
    apply htailSurfaceFix
    rintro ⟨u,hux,huSq⟩
    obtain ⟨q,hq,hqx⟩ := hx
    have hxs : x ∈ en.source := hux ▸ (hersource ▸ u.property)
    have hex : en x = q := by rw [← hqx,en.right_inv (hentarget ▸ Set.mem_univ q)]
    apply hrepairAvoid q (Or.inl hq)
    change replacementChart (en u.val) ∈ Schoenflies.Plane.openSquare 0 1 at huSq
    rw [hux,hex] at huSq
    exact huSq
  have hprefixFullSource : prefixSurface.finalMap '' b.val.image ⊆ en.source := by
    rintro z ⟨x,hx,rfl⟩
    have hxs : x ∈ en.source := by
      apply hsource_all true
      change x ∈ cb.image
      rw [hcb_image]; exact hx
    have hh := hprefixSurfaceCoord (⟨1,by norm_num⟩ : Interval) ⟨x,hxs⟩
    change prefixSurface.finalMap x = (prefixLift.finalMap ⟨x,hxs⟩ : S) at hh
    rw [hh]
    exact (prefixLift.finalMap ⟨x,hxs⟩).property
  have hinverse_image (T : Set S) (hT : T ⊆ en.source) : en.symm '' (en '' T) = T := by
    ext x
    constructor
    · rintro ⟨z,⟨y,hy,hyz⟩,hzx⟩
      have he : y = x := (en.left_inv (hT hy)).symm.trans (congrArg en.symm hyz |>.trans hzx)
      exact he ▸ hy
    · intro hx
      exact ⟨en x,⟨x,hx,rfl⟩,en.left_inv (hT hx)⟩
  have hAwhole : en.symm '' X false = a.val.image := by
    change en.symm '' (en '' ca.image) = a.val.image
    rw [hca_image]
    exact hinverse_image _ (fun x hx => hsource_all false (hca_image.symm ▸ hx))
  have hBwhole : en.symm '' (prefixHomeo '' X true) = prefixSurface.finalMap '' b.val.image := by
    rw [← hprefixImageCoord]
    exact hinverse_image _ hprefixFullSource
  have htailCentralImage : tailSurface.finalMap '' (en.symm '' segment ℝ qcore (-qcore)) =
      en.symm '' segment ℝ qcore (-qcore) := by
    apply Set.Subset.antisymm
    · rintro x ⟨y,hy,hxy⟩
      have he := htailCentral (⟨1,by norm_num⟩ : Interval) y hy
      exact (he.symm.trans hxy) ▸ hy
    · intro x hx
      exact ⟨x,hx,htailCentral (⟨1,by norm_num⟩ : Interval) x hx⟩
  have htailWholeImage : tailSurface.finalMap '' (prefixSurface.finalMap '' b.val.image) = a.val.image := by
    rw [← hBwhole,← hcoverB,Set.image_union,Set.image_union,htailCentralImage,htailSurfaceImage,
      ← Set.image_union,hcoverA,hAwhole]
  have htailRel : MarkedIsotopyRel M (prefixSurface.finalMap '' b.val.image) a.val.image :=
    ⟨tailSurface,htailMarks,htailWholeImage⟩
  apply Quotient.sound
  change MarkedIsotopyRel M a.val.image b.val.image
  exact (markedIsotopy_equivalence M).symm ((markedIsotopy_equivalence M).trans hprefixRel htailRel)

end CurveComplex.HyperellipticModel
