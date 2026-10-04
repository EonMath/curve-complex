import CurveComplexGenusTwo.Topology.SDRStaticModel.ModelAnnulusEndpointPROVED
import CurveComplexGenusTwo.Topology.OriginalCircleCollar.CircleCollarOriginalPackage
import Mathlib.Topology.Algebra.GroupWithZero
import CurveComplexGenusTwo.Topology.Smoothing.FiniteIsotopyAssembly
import Mathlib.Topology.Connected.Clopen
import CurveComplexGenusTwo.Topology.ActualSeparatingNonadjacency.OriginalSeparatingNonadjacencyProof
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualStandardTorusSurface
import CurveComplexGenusTwo.Topology.CapBandGeometry.DiskOpen
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualIntegerBasisTorusHomeomorph
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualLiftedAxisChart
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalGenusTwoSeparatingActualCut
import CurveComplexGenusTwo.Topology.ActualCutRecognition.SharedActualCut
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalClassificationStatements
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualTranslatedPrimitiveSource
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleProjectionEssential
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12FullConnectivity
import CurveComplexGenusTwo.Foundations.NonseparatingRealizationBridge
import CurveComplexGenusTwo.Topology.FareyDictionaryStarDeletionConsumer

set_option maxHeartbeats 20000000
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplex.Hyperbolic CurveComplexGenusTwo.Topology
open Set _root_.Topology CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open LeanEval.Topology.ClassificationOfSurfaces Schoenflies
open CurveComplexGenusTwo.Topology.PuncturedTorusCandidate
open scoped Manifold ContDiff

theorem source_genus_two_separating_farey_dictionary
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (v : {u : Vertex S // IsSeparatingVertex S u}) :
    letI : DecidableEq (Vertex S) := Classical.decEq _
    Nonempty (FareyJoinLinkDictionary (curveComplex S 1) geometricIntersection v.1) := by
  classical
  letI : DecidableEq (Vertex S) := Classical.decEq _
  have hsep : ∀ a b : Vertex S, IsSeparatingVertex S a →
      IsSeparatingVertex S b → a ≠ b → 1 < geometricIntersection a b := by
    exact source_genus_two_separating_vertices_nonadjacent S hS
  classical
  letI : DecidableEq (Vertex S) := Classical.decEq _
  have hsmall : ∀ a b : Vertex S, IsSeparatingVertex S a →
      geometricIntersection a b ≤ 1 → geometricIntersection a b = 0 := by
    letI : ClosedSurface S := Classical.choice hS.2.1
    have hOneCrossing (a b : Curve S) (ht : Transverse a b)
        (hcard : ht.1.toFinset.card = 1) : Nonseparating a := by
      classical
      let : ClosedSurface S := Classical.choice hS.2.1
      let : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
      have hlocal (p : S) (hp : p ∈ a.image) :
          ∃ C : SurfaceLocalSides (Set.univ : Set S) a.image, p ∈ C.nbhd := by
        obtain ⟨U,V,hpU,h,hU,hV,hzero,haxis⟩ := LocalSurgery.embedded_curve_has_local_axis_chart a p hp
        have h0V : ((0,0) : ℝ × ℝ) ∈ V := hzero ▸ (h ⟨p,hpU⟩).property
        obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
        let δ : ℝ := r/2
        have hδ : 0 < δ := half_pos hr
        let J := Set.Icc (-δ) δ
        have hqV (z : J × J) : ((z.2:ℝ),(z.1:ℝ)) ∈ V := by
          apply hrV
          rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
          have hz0 : |(z.1:ℝ)| ≤ δ := abs_le.mpr z.1.property
          have hz1 : |(z.2:ℝ)| ≤ δ := abs_le.mpr z.2.property
          constructor <;> dsimp [δ] at * <;> linarith
        let q : J × J → V := fun z => ⟨((z.2:ℝ),(z.1:ℝ)),hqV z⟩
        have hq : Continuous q := (by fun_prop : Continuous (fun z : J × J => ((z.2:ℝ),(z.1:ℝ)))).subtype_mk _
        have hqi : Function.Injective q := by
          intro x y he
          have hh := congrArg Subtype.val he
          exact Prod.ext (Subtype.ext (congrArg Prod.snd hh)) (Subtype.ext (congrArg Prod.fst hh))
        let B : J × J → S := fun z => (h.symm (q z)).val
        have hB : IsEmbedding B := by
          have hcont : Continuous B := continuous_subtype_val.comp (h.symm.continuous.comp hq)
          have hinj : Function.Injective B :=
            Subtype.val_injective.comp (h.symm.injective.comp hqi)
          exact (hcont.isClosedEmbedding hinj).isEmbedding
        have hBP (z : J × J) : B z ∈ a.image ↔ (z.2:ℝ) = 0 := by
          have hh := haxis (B z) (h.symm (q z)).property
          have he : h ⟨B z,(h.symm (q z)).property⟩ = q z := h.apply_symm_apply (q z)
          rw [he] at hh
          exact hh
        obtain ⟨C,hcenter⟩ := source_embedded_rectangle_local_sides
          (by linarith : -δ < δ) (neg_lt_zero.mpr hδ) hδ B hB
          Set.univ a.image (Set.subset_univ _) hBP
        let z : J := ⟨0,⟨by linarith,by linarith⟩⟩
        have hBp : B (z,z) = p := by
          have he : q (z,z) = h ⟨p,hpU⟩ := by
            apply Subtype.ext
            exact hzero.symm
          dsimp [B]
          rw [he,h.symm_apply_apply]
        exact ⟨C,hBp ▸ hcenter z (by dsimp [z]; linarith) (by dsimp [z]; linarith)⟩
      obtain ⟨p,hp,hcross,hunique⟩ := unique_crossing_chart_of_count_one a b ht hcard
      obtain ⟨U,V,hpU,h,hU,hV,hzero,haxes⟩ := hcross
      have h0V : ((0,0) : ℝ × ℝ) ∈ V := hzero ▸ (h ⟨p,hpU⟩).property
      obtain ⟨r,hr,hrV⟩ := Metric.isOpen_iff.mp hV (0,0) h0V
      let δ : ℝ := r/2
      have hδ : 0 < δ := half_pos hr
      let J := Set.Icc (-δ) δ
      have hqV (z : J × J) : ((z.2:ℝ),(z.1:ℝ)) ∈ V := by
        apply hrV
        rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
        have hz0 : |(z.1:ℝ)| ≤ δ := abs_le.mpr z.1.property
        have hz1 : |(z.2:ℝ)| ≤ δ := abs_le.mpr z.2.property
        constructor <;> dsimp [δ] at * <;> linarith
      let q : J × J → V := fun z => ⟨((z.2:ℝ),(z.1:ℝ)),hqV z⟩
      have hq : Continuous q := (by fun_prop : Continuous (fun z : J × J => ((z.2:ℝ),(z.1:ℝ)))).subtype_mk _
      have hqi : Function.Injective q := by
        intro x y he
        have hh := congrArg Subtype.val he
        exact Prod.ext (Subtype.ext (congrArg Prod.snd hh)) (Subtype.ext (congrArg Prod.fst hh))
      let B : J × J → S := fun z => (h.symm (q z)).val
      have hB : IsEmbedding B := by
        have hcont : Continuous B := continuous_subtype_val.comp (h.symm.continuous.comp hq)
        have hinj : Function.Injective B := Subtype.val_injective.comp (h.symm.injective.comp hqi)
        exact (hcont.isClosedEmbedding hinj).isEmbedding
      have hBaxes (z : J × J) :
          (B z ∈ a.image ↔ (z.2:ℝ) = 0) ∧ (B z ∈ b.image ↔ (z.1:ℝ) = 0) := by
        have hh := haxes (B z) (h.symm (q z)).property
        have he : h ⟨B z,(h.symm (q z)).property⟩ = q z := h.apply_symm_apply (q z)
        rw [he] at hh
        exact hh
      let clip : Plane → J × J := fun z =>
        (Set.projIcc (-δ) δ (by linarith) (z 0),Set.projIcc (-δ) δ (by linarith) (z 1))
      let F : Plane → S := B ∘ clip
      have hFc : Continuous F := hB.continuous.comp
        ((continuous_projIcc.comp (by fun_prop)).prodMk (continuous_projIcc.comp (by fun_prop)))
      let N : Set Plane := thetaRect (-δ) δ (-δ) δ
      let Tminus : Set Plane := thetaRect (-δ) δ (-δ) 0
      let Tplus : Set Plane := thetaRect (-δ) δ 0 δ
      have hclip (z : Plane) (hz : z ∈ N) :
          ((clip z).1:ℝ) = z 0 ∧ ((clip z).2:ℝ) = z 1 := by
        exact ⟨by simp [clip,Set.projIcc_of_mem (show -δ ≤ δ by linarith) ⟨hz.1.le,hz.2.1.le⟩],
          by simp [clip,Set.projIcc_of_mem (show -δ ≤ δ by linarith) ⟨hz.2.2.1.le,hz.2.2.2.le⟩]⟩
      have hFi : InjOn F N := by
        intro z hz w hw he
        have hh := hB.injective he
        have h0 := congrArg (fun t : J × J => (t.1:ℝ)) hh
        have h1 := congrArg (fun t : J × J => (t.2:ℝ)) hh
        rw [(hclip z hz).1,(hclip w hw).1] at h0
        rw [(hclip z hz).2,(hclip w hw).2] at h1
        ext i
        fin_cases i <;> assumption
      have hFaxes (z : Plane) (hz : z ∈ N) :
          (F z ∈ a.image ↔ z 1 = 0) ∧ (F z ∈ b.image ↔ z 0 = 0) := by
        change (B (clip z) ∈ a.image ↔ z 1 = 0) ∧ (B (clip z) ∈ b.image ↔ z 0 = 0)
        simpa only [(hclip z hz).1,(hclip z hz).2] using hBaxes (clip z)
      have hNzero : (0 : Plane) ∈ N := by
        change -δ < 0 ∧ 0 < δ ∧ -δ < 0 ∧ 0 < δ
        exact ⟨by linarith,hδ,by linarith,hδ⟩
      have hFzero : F 0 = p := by
        have he : q (clip 0) = h ⟨p,hpU⟩ := by
          apply Subtype.ext
          rw [hzero]
          exact Prod.ext (hclip 0 hNzero).2 (hclip 0 hNzero).1
        change (h.symm (q (clip 0))).val = p
        rw [he,h.symm_apply_apply]
      have hTmN : Tminus ⊆ N := fun z hz => ⟨hz.1,hz.2.1,hz.2.2.1,hz.2.2.2.trans hδ⟩
      have hTpN : Tplus ⊆ N := fun z hz => ⟨hz.1,hz.2.1,(neg_lt_zero.mpr hδ).trans hz.2.2.1,hz.2.2.2⟩
      let C0 : SurfaceLocalSides (Set.univ : Set S) a.image := {
        nbhd := F '' N
        left := F '' Tminus
        right := F '' Tplus
        isOpen_nbhd := surface_invariance_of_domain_probe F N (thetaRect_open _ _ _ _) hFc.continuousOn hFi
        nbhd_subset := Set.subset_univ _
        nbhd_diff := by
          ext x
          constructor
          · rintro ⟨⟨z,hz,rfl⟩,hna⟩
            have hzne : z 1 ≠ 0 := fun he => hna ((hFaxes z hz).1.mpr he)
            rcases lt_or_gt_of_ne hzne with hneg|hpos
            · exact Or.inl ⟨z,⟨hz.1,hz.2.1,hz.2.2.1,hneg⟩,rfl⟩
            · exact Or.inr ⟨z,⟨hz.1,hz.2.1,hpos,hz.2.2.2⟩,rfl⟩
          · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
            · exact ⟨⟨z,hTmN hz,rfl⟩,fun ha => (ne_of_lt hz.2.2.2) ((hFaxes z (hTmN hz)).1.mp ha)⟩
            · exact ⟨⟨z,hTpN hz,rfl⟩,fun ha => (ne_of_gt hz.2.2.1) ((hFaxes z (hTpN hz)).1.mp ha)⟩
        connected_left := (thetaRect_connected (by linarith) (by linarith : -δ < 0)).image F hFc.continuousOn
        connected_right := (thetaRect_connected (by linarith) hδ).image F hFc.continuousOn
        limit_left := by
          rintro x ⟨⟨z,hz,rfl⟩,hza⟩
          have hz1 : z 1 = 0 := (hFaxes z hz).1.mp hza
          have he : z = Plane.mk (z 0) 0 := by ext i; fin_cases i; rfl; exact hz1
          rw [he]
          exact hFc.continuousWithinAt.mem_closure_image
            ((thetaRect_center_mem_closure ⟨hz.1,hz.2.1⟩ (by linarith : -δ < 0) hδ).1)
        limit_right := by
          rintro x ⟨⟨z,hz,rfl⟩,hza⟩
          have hz1 : z 1 = 0 := (hFaxes z hz).1.mp hza
          have he : z = Plane.mk (z 0) 0 := by ext i; fin_cases i; rfl; exact hz1
          rw [he]
          exact hFc.continuousWithinAt.mem_closure_image
            ((thetaRect_center_mem_closure ⟨hz.1,hz.2.1⟩ (by linarith : -δ < 0) hδ).2) }
      let zm : Plane := Plane.mk 0 (-δ/2)
      let zp : Plane := Plane.mk 0 (δ/2)
      let l := F zm
      let r' := F zp
      have hzm : zm ∈ Tminus := by change -δ < 0 ∧ 0 < δ ∧ -δ < -δ/2 ∧ -δ/2 < 0; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
      have hzp : zp ∈ Tplus := by change -δ < 0 ∧ 0 < δ ∧ 0 < δ/2 ∧ δ/2 < δ; exact ⟨by linarith,by linarith,by linarith,by linarith⟩
      have hlC : l ∈ C0.left := ⟨zm,hzm,rfl⟩
      have hrC : r' ∈ C0.right := ⟨zp,hzp,rfl⟩
      have hlb : l ∈ b.image := (hFaxes zm (hTmN hzm)).2.mpr rfl
      have hrb : r' ∈ b.image := (hFaxes zp (hTpN hzp)).2.mpr rfl
      have hlne : l ≠ p := by
        intro he
        have hz : zm = 0 := hFi (hTmN hzm) hNzero (he.trans hFzero.symm)
        have hh := congrArg (fun z : Plane => z 1) hz
        change -δ/2=0 at hh
        linarith
      have hrne : r' ≠ p := by
        intro he
        have hz : zp = 0 := hFi (hTpN hzp) hNzero (he.trans hFzero.symm)
        have hh := congrArg (fun z : Plane => z 1) hz
        change δ/2=0 at hh
        linarith
      let T : Set S := b.image \ {p}
      have hT : IsConnected T := by
        obtain ⟨z,hz⟩ := hp.2
        have he : T = b.map '' ({z}ᶜ : Set Circle) := by
          ext x
          constructor
          · rintro ⟨⟨w,hw⟩,hxp⟩
            refine ⟨w,?_,hw⟩
            intro hwz
            exact hxp (Set.mem_singleton_iff.mpr (by rw [← hw,hwz,hz]))
          · rintro ⟨w,hw,rfl⟩
            exact ⟨Set.mem_range_self w,fun he => hw (b.embedded.injective ((Set.mem_singleton_iff.mp he).trans hz.symm))⟩
        rw [he]
        exact (Circle.isPathConnected_compl_singleton z).isConnected.image b.map b.embedded.continuous.continuousOn
      let Q : Set S := Set.univ \ a.image
      have hTQ : T ⊆ Q := by
        intro x hx
        refine ⟨Set.mem_univ _,?_⟩
        intro hxa
        exact hx.2 (Set.mem_singleton_iff.mpr (hunique x ⟨hxa,hx.1⟩))
      have hlT : l ∈ T := ⟨hlb,fun he => hlne (Set.mem_singleton_iff.mp he)⟩
      have hrT : r' ∈ T := ⟨hrb,fun he => hrne (Set.mem_singleton_iff.mp he)⟩
      have hrL : r' ∈ connectedComponentIn Q l := hT.isPreconnected.subset_connectedComponentIn hlT hTQ hrT
      have hC0 : C0.nbhd \ a.image ⊆ connectedComponentIn Q l ∪ connectedComponentIn Q l := by
        rw [C0.nbhd_diff]
        apply union_subset
        · intro x hx
          exact Or.inl (C0.connected_left.isPreconnected.subset_connectedComponentIn hlC C0.left_subset_diff hx)
        · intro x hx
          have hh := C0.connected_right.isPreconnected.subset_connectedComponentIn hrC C0.right_subset_diff hx
          rw [← connectedComponentIn_eq hrL] at hh
          exact Or.inl hh
      have hclosed : IsClosed a.image := (isCompact_range a.embedded.continuous).isClosed
      have hconn : IsConnected ((Set.univ : Set S) ∩ a.image) := by rw [Set.univ_inter]; exact isConnected_range a.embedded.continuous
      have hpC0 : p ∈ C0.nbhd := ⟨0,hNzero,hFzero⟩
      have hall := theta_exhaustion_from_start_local_sides isOpen_univ isPreconnected_univ hclosed hconn
        (fun x hx => hlocal x hx.2) C0 p ⟨Set.mem_univ _,hp.1⟩ hpC0 l l (hTQ hlT) hC0
      have heq : Q = connectedComponentIn Q l := Set.Subset.antisymm
        (fun x hx => (hall x hx).elim id id) (connectedComponentIn_subset _ _)
      change IsConnected a.imageᶜ
      have hconnQ : IsConnected Q := heq.symm ▸ isConnected_connectedComponentIn_iff.mpr (hTQ hlT)
      simpa only [Q,← Set.compl_eq_univ_sdiff] using hconnQ
    intro a b ha hle
    by_contra hzero
    have hone : geometricIntersection a b = 1 := by omega
    obtain ⟨c,d,hc,hd,ht,hcard⟩ := source_geometric_intersection_attained S a b
    have hcns : Nonseparating c.val := hOneCrossing c.val d.val ht (hcard.trans hone)
    obtain ⟨e,he,hdisc⟩ := ha
    have hrel : (essentialCurveSetoid S).r c e := Quotient.exact (hc.trans he.symm)
    exact hdisc ((nonseparating_isotopy_invariant hrel).mp hcns)
  have hfixed (c : EssentialCurve S) (w : Vertex S)
      (hzero : geometricIntersection (Quotient.mk (essentialCurveSetoid S) c) w = 0) :
      ∃ d : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) d = w ∧
        Disjoint c.val.image d.val.image := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨a,d,ha,hd,ht,hcard⟩ := source_geometric_intersection_attained S
      (Quotient.mk (essentialCurveSetoid S) c) w
    have hdis : Disjoint a.val.image d.val.image := by
      rw [Set.disjoint_iff_inter_eq_empty]
      have he : ht.1.toFinset = ∅ := Finset.card_eq_zero.mp (hcard.trans hzero)
      exact Set.Finite.toFinset_eq_empty.mp he
    have hac : AmbientIsotopy.Rel a.val.image c.val.image := Quotient.exact ha
    obtain ⟨H,hH⟩ := hac
    obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
    let out : Curve S := ⟨e ∘ d.val.map,e.isEmbedding.comp d.val.embedded⟩
    have hOut : out.image = H.finalMap '' d.val.image := by
      change Set.range (e ∘ d.val.map) = H.finalMap '' Set.range d.val.map
      rw [Set.range_comp]
      exact Set.image_congr (fun x _ => he x)
    have hdout : AmbientIsotopy.Rel d.val.image out.image := ⟨H,hOut.symm⟩
    let outc : EssentialCurve S := ⟨out,(essential_isotopy_invariant hdout).mp d.property⟩
    refine ⟨outc,(Quotient.sound hdout).symm.trans hd,?_⟩
    change Disjoint c.val.image out.image
    rw [← hH,hOut]
    apply Set.disjoint_left.mpr
    rintro x ⟨y,hy,hyx⟩ ⟨z,hz,hzx⟩
    have heq : y=z := e.injective (by rw [he y,he z];exact hyx.trans hzx.symm)
    exact Set.disjoint_left.mp hdis hy (heq ▸ hz)
  classical
  obtain ⟨c,hcv,hdiv⟩ := v.property
  obtain ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV,hTU,hTV⟩ :=
    source_genus_two_separating_actual_cut S hS c.val c.property hdiv
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hCollapse (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p) :
      ∃ q : C(S,Torus), (∀ x : U, q x.val = (e x).val) ∧
        (∀ x, x ∉ U → q x = p) := by
    classical
    let q : S → Torus := fun x => if hx : x ∈ U then (e ⟨x,hx⟩).val else p
    have hqU (x : U) : q x.val=(e x).val := by simp [q,x.property]
    have hqOut (x : S) (hx : x ∉ U) : q x=p := by simp [q,hx]
    have hq : Continuous q := by
      apply continuous_def.mpr
      intro O hO
      by_cases hp : p ∈ O
      · let K : Set Torus := Oᶜ
        have hK : IsCompact K := hO.isClosed_compl.isCompact
        letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
        have hKp : ∀ x ∈ K, x ≠ p := by
          intro x hx he
          exact hx (he ▸ hp)
        let f : K → S := fun x => (e.symm ⟨x.val,hKp x.val x.property⟩).val
        have hf : Continuous f := continuous_subtype_val.comp
          (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
        have hr : IsCompact (range f) := isCompact_range hf
        have heq : q ⁻¹' O = (range f)ᶜ := by
          ext x
          constructor
          · intro hx
            rintro ⟨y,hy⟩
            have hxU : x ∈ U := hy ▸ (e.symm ⟨y.val,hKp y.val y.property⟩).property
            have hqv : q x=y.val := by
              rw [←hy,hqU]
              exact congrArg Subtype.val (e.apply_symm_apply _)
            exact y.property (hqv ▸ hx)
          · intro hx
            change q x ∈ O
            by_cases hxU : x ∈ U
            · rw [show q x=(e ⟨x,hxU⟩).val from hqU ⟨x,hxU⟩]
              by_contra hn
              apply hx
              refine ⟨⟨(e ⟨x,hxU⟩).val,hn⟩,?_⟩
              change (e.symm (e ⟨x,hxU⟩)).val=x
              rw [e.symm_apply_apply]
            · rw [hqOut x hxU]
              exact hp
        rw [heq]
        exact hr.isClosed.isOpen_compl
      · have heq : q ⁻¹' O = Subtype.val ''
            ((fun x : U => (e x).val) ⁻¹' O) := by
          ext x
          constructor
          · intro hx
            have hxU : x ∈ U := by
              by_contra hn
              exact hp ((hqOut x hn) ▸ hx)
            refine ⟨⟨x,hxU⟩,?_,rfl⟩
            change (e ⟨x,hxU⟩).val ∈ O
            change q x ∈ O at hx
            rw [hqU ⟨x,hxU⟩] at hx
            exact hx
          · rintro ⟨y,hy,rfl⟩
            change q y.val ∈ O
            change (e y).val ∈ O at hy
            rw [hqU y]
            exact hy
        rw [heq]
        exact hU.isOpenMap_subtype_val _ (hO.preimage
          (continuous_subtype_val.comp e.continuous))
    exact ⟨⟨q,hq⟩,hqU,hqOut⟩
  have hProjectedNS (c : Curve S) (π : C(S,Circle))
      (hπ : ∀ z, π (c.map z)=z) : Nonseparating c := by
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    have hc : Essential c := actual_circle_projected_curve_is_essential c π hπ
    by_contra hsep
    obtain ⟨e,he,hcore⟩ := LocalSurgery.actual_original_essential_circle_has_annular_collar
      S 2 (by omega) hS ⟨c,hc⟩
    have hz := source_separating_curve_actual_annular_fundamental_zero S hS c hsep e he hcore
    let f : TopCat.of Circle ⟶ TopCat.of S := TopCat.ofHom ⟨c.map,c.embedded.continuous⟩
    let g : TopCat.of S ⟶ TopCat.of Circle := TopCat.ofHom π
    have hfg : f ≫ g = 𝟙 (TopCat.of Circle) := by
      ext z
      exact congrArg (fun z : Circle => (z : ℂ)) (hπ z)
    have hcomp := congrArg (fun k => HomologicalComplex.homologyMap
      (actualSingularFunctor.map k) 1) hfg
    rw [actualSingularFunctor.map_comp,HomologicalComplex.homologyMap_comp,
      actualSingularFunctor.map_id,HomologicalComplex.homologyMap_id] at hcomp
    have hclass := congrArg (fun k => k CircleFundamentalCycle.fundamentalClass) hcomp
    change HomologicalComplex.homologyMap (actualSingularFunctor.map g) 1
      (HomologicalComplex.homologyMap (actualSingularFunctor.map f) 1
        CircleFundamentalCycle.fundamentalClass)=CircleFundamentalCycle.fundamentalClass at hclass
    rw [hz,map_zero] at hclass
    have hcoord := CircleFundamentalCycle.fundamentalClass_coordinate
    rw [←hclass,map_zero] at hcoord
    norm_num at hcoord
  have hSideEssential (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p)
      (c : Curve S) (a : Torus) (m n : ℤ) (hgcd : m.gcd n=1)
      (hcurve : ∀ z, ∃ x : U, x.val=c.map z ∧ (e x).val=a*torusWindingMap m n z) :
      Essential c ∧ Nonseparating c := by
    have hcollapse : ∃ q : C(S,Torus), (∀ x : U, q x.val = (e x).val) ∧
        (∀ x, x ∉ U → q x = p) := by
      classical
      let q : S → Torus := fun x => if hx : x ∈ U then (e ⟨x,hx⟩).val else p
      have hqU (x : U) : q x.val=(e x).val := by simp [q,x.property]
      have hqOut (x : S) (hx : x ∉ U) : q x=p := by simp [q,hx]
      have hq : Continuous q := by
        apply continuous_def.mpr
        intro O hO
        by_cases hp : p ∈ O
        · let K : Set Torus := Oᶜ
          have hK : IsCompact K := hO.isClosed_compl.isCompact
          letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
          have hKp : ∀ x ∈ K, x ≠ p := by
            intro x hx he
            exact hx (he ▸ hp)
          let f : K → S := fun x => (e.symm ⟨x.val,hKp x.val x.property⟩).val
          have hf : Continuous f := continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
          have hr : IsCompact (range f) := isCompact_range hf
          have heq : q ⁻¹' O = (range f)ᶜ := by
            ext x
            constructor
            · intro hx
              rintro ⟨y,hy⟩
              have hxU : x ∈ U := hy ▸ (e.symm ⟨y.val,hKp y.val y.property⟩).property
              have hqv : q x=y.val := by
                rw [←hy,hqU]
                exact congrArg Subtype.val (e.apply_symm_apply _)
              exact y.property (hqv ▸ hx)
            · intro hx
              change q x ∈ O
              by_cases hxU : x ∈ U
              · rw [show q x=(e ⟨x,hxU⟩).val from hqU ⟨x,hxU⟩]
                by_contra hn
                apply hx
                refine ⟨⟨(e ⟨x,hxU⟩).val,hn⟩,?_⟩
                change (e.symm (e ⟨x,hxU⟩)).val=x
                rw [e.symm_apply_apply]
              · rw [hqOut x hxU]
                exact hp
          rw [heq]
          exact hr.isClosed.isOpen_compl
        · have heq : q ⁻¹' O = Subtype.val ''
              ((fun x : U => (e x).val) ⁻¹' O) := by
            ext x
            constructor
            · intro hx
              have hxU : x ∈ U := by
                by_contra hn
                exact hp ((hqOut x hn) ▸ hx)
              refine ⟨⟨x,hxU⟩,?_,rfl⟩
              change (e ⟨x,hxU⟩).val ∈ O
              change q x ∈ O at hx
              rw [hqU ⟨x,hxU⟩] at hx
              exact hx
            · rintro ⟨y,hy,rfl⟩
              change q y.val ∈ O
              change (e y).val ∈ O at hy
              rw [hqU y]
              exact hy
          rw [heq]
          exact hU.isOpenMap_subtype_val _ (hO.preimage
            (continuous_subtype_val.comp e.continuous))
      exact ⟨⟨q,hq⟩,hqU,hqOut⟩
    obtain ⟨q,hq,hqOut⟩ := hcollapse
    let u := Int.gcdA m n
    let v := Int.gcdB m n
    have hbez : m*u+n*v=1 := by
      have h := Int.gcd_eq_gcd_ab m n
      rw [hgcd] at h
      exact h.symm
    let χ : C(Torus,Circle) := ⟨fun w => (a.1⁻¹*w.1)^u*(a.2⁻¹*w.2)^v,by fun_prop⟩
    have hcoordinate : ∀ z, (χ.comp q) (c.map z)=z := by
      intro z
      obtain ⟨x,hxc,hxz⟩ := hcurve z
      have hh : q (c.map z)=a*torusWindingMap m n z := by rw [←hxc,hq x];exact hxz
      change (a.1⁻¹*(q (c.map z)).1)^u*(a.2⁻¹*(q (c.map z)).2)^v=z
      rw [hh]
      simp only [Prod.fst_mul,Prod.snd_mul,torusWindingMap,← mul_assoc,inv_mul_cancel,mul_one,one_mul]
      rw [← zpow_mul,← zpow_mul,← zpow_add,hbez,zpow_one]
    exact ⟨actual_circle_projected_curve_is_essential c (χ.comp q) hcoordinate,
      hProjectedNS c (χ.comp q) hcoordinate⟩
  have hSlopeInject (Q : C(S,Torus))
      (C : FareySlope → Curve S) (A : FareySlope → Torus)
      (hC : ∀ s z, Q ((C s).map z)=A s*torusWindingMap (slopeDirection s).1 (slopeDirection s).2 z)
      (s t : FareySlope) (h : AmbientIsotopy.Rel (C s).image (C t).image) : s=t := by
    have power_zero (k : ℤ)
        (h : (⟨fun z : Circle => z ^ k, continuous_zpow k⟩ : C(Circle, Circle)).Nullhomotopic) :
        k = 0 := by
      obtain ⟨r, ⟨H⟩⟩ := h
      obtain ⟨r₀, hr₀⟩ := Circle.exp_surjective r
      let G := H.symm
      let L : C(unitInterval × Circle, ℝ) := Circle.isCoveringMap_exp.liftHomotopy
        G.toContinuousMap (ContinuousMap.const Circle r₀)
        (fun z => (G.apply_zero z).trans hr₀.symm)
      have hL (t : unitInterval) (z : Circle) : Circle.exp (L (t, z)) = G (t, z) :=
        congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts G.toContinuousMap
          (ContinuousMap.const Circle r₀) _) (t, z)
      let F : C(Circle, ℝ) := ⟨fun z => L (1, z), L.continuous.comp
        (continuous_const.prodMk continuous_id)⟩
      have hF (z : Circle) : Circle.exp (F z) = z ^ k :=
        (hL 1 z).trans (G.apply_one z)
      let γ : C(unitInterval, Circle) :=
        ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      let δ : C(unitInterval, Circle) := ⟨fun t => (γ t) ^ k, (continuous_zpow k).comp γ.continuous⟩
      let Γ : C(unitInterval, ℝ) := F.comp γ
      let Λ : C(unitInterval, ℝ) := ⟨fun t => Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      have hΓlift : Circle.exp ∘ Γ = δ := by
        funext t
        exact hF (γ t)
      have hΛlift : Circle.exp ∘ Λ = δ := by
        funext t
        change Circle.exp (Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ))) = (γ t) ^ k
        rw [Circle.exp_add]
        have hΓ0 : Circle.exp (Γ 0) = 1 := by
          have hh := congrFun hΓlift 0
          simpa [δ, γ] using hh
        rw [hΓ0, one_mul]
        simpa only [zsmul_eq_mul, γ, ContinuousMap.coe_mk] using
          Circle.exp_zsmul (2 * Real.pi * (t : ℝ)) k
      have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
      have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
      have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
      have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
      have hloop : Γ 1 = Γ 0 := by
        change F (γ 1) = F (γ 0)
        congr 1
        simp [γ]
      rw [hloop] at hend
      have he : (k : ℝ) * (2 * Real.pi) = 0 := by
        have hh : Γ 0 = Γ 0 + (k : ℝ) * (2 * Real.pi) := by simpa [Λ] using hend
        linarith
      have hk : (k : ℝ) = 0 := (mul_eq_zero.mp he).resolve_right
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact_mod_cast hk
    have transfer {S : Type} [TopologicalSpace S] (c d : Curve S) (χ : C(S, Circle))
        (h : AmbientIsotopy.Rel c.image d.image)
        (hd : (χ.comp ⟨d.map, d.embedded.continuous⟩).Nullhomotopic) :
        (χ.comp ⟨c.map, c.embedded.continuous⟩).Nullhomotopic := by
      obtain ⟨H, hH⟩ := h
      have hr (z : Circle) : H.finalMap (c.map z) ∈ Set.range d.map := by
        rw [show Set.range d.map = d.image from rfl, ← hH]
        exact ⟨c.map z, ⟨z, rfl⟩, rfl⟩
      let η : C(Circle, Circle) := ⟨fun z => d.embedded.toHomeomorph.symm
        ⟨H.finalMap (c.map z), hr z⟩,
        d.embedded.toHomeomorph.symm.continuous.comp
          ((H.map.continuous.comp (continuous_const.prodMk c.embedded.continuous)).subtype_mk _)⟩
      have hη (z : Circle) : d.map (η z) = H.finalMap (c.map z) :=
        congrArg Subtype.val (d.embedded.toHomeomorph.apply_symm_apply
          ⟨H.finalMap (c.map z), hr z⟩)
      let G : (χ.comp ⟨c.map, c.embedded.continuous⟩).Homotopy
          ((χ.comp ⟨d.map, d.embedded.continuous⟩).comp η) := {
        toContinuousMap := ⟨fun tz => χ (H.map (tz.1, c.map tz.2)),
          χ.continuous.comp (H.map.continuous.comp
            (continuous_fst.prodMk (c.embedded.continuous.comp continuous_snd)))⟩
        map_zero_left := by
          intro z
          change χ (H.map (⟨0, by norm_num⟩, c.map z)) = χ (c.map z)
          rw [H.at_zero (c.map z)]
        map_one_left := by
          intro z
          change χ (H.finalMap (c.map z)) = χ (d.map (η z))
          rw [hη] }
      obtain ⟨r, hr⟩ := hd.comp_left η
      exact ⟨r, ContinuousMap.Homotopic.trans ⟨G⟩ hr⟩
    let χ : C(Torus,Circle) := ⟨fun x => x.1^(slopeDirection t).2*x.2^(-(slopeDirection t).1),by fun_prop⟩
    have hχmul (x y : Torus) : χ (x*y)=χ x*χ y := by
      dsimp [χ]
      simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
      ac_rfl
    have χw (i j : ℤ) (z : Circle) : χ (torusWindingMap i j z)=
        z^(i*(slopeDirection t).2-j*(slopeDirection t).1) := by
      change (z^i)^(slopeDirection t).2*(z^j)^(-(slopeDirection t).1)=_
      rw [←zpow_mul,←zpow_mul,←zpow_add]
      congr 1
      ring
    have ht : ((χ.comp Q).comp ⟨(C t).map,(C t).embedded.continuous⟩).Nullhomotopic := by
      have heq : (χ.comp Q).comp ⟨(C t).map,(C t).embedded.continuous⟩ =
          ContinuousMap.const Circle (χ (A t)) := by
        apply ContinuousMap.ext
        intro z
        change χ (Q ((C t).map z))=χ (A t)
        rw [hC,hχmul,χw]
        simp [mul_comm]
      rw [heq]
      exact ContinuousMap.nullhomotopic_of_constant _
    have hs := transfer (C s) (C t) (χ.comp Q) h ht
    let normalize : C(Circle,Circle) := ⟨fun z => (χ (A s))⁻¹*z,by fun_prop⟩
    have hpower := hs.comp_right normalize
    have heq : normalize.comp ((χ.comp Q).comp ⟨(C s).map,(C s).embedded.continuous⟩) =
        (⟨fun z : Circle => z^((slopeDirection s).1*(slopeDirection t).2-
          (slopeDirection s).2*(slopeDirection t).1),continuous_zpow _⟩ : C(Circle,Circle)) := by
      apply ContinuousMap.ext
      intro z
      change (χ (A s))⁻¹*χ (Q ((C s).map z))=_
      rw [hC,hχmul,χw,←mul_assoc,inv_mul_cancel,one_mul]
      rfl
    rw [heq] at hpower
    have hzero := power_zero _ hpower
    cases s with
    | none =>
      cases t with
      | none => rfl
      | some q =>
        simp [slopeDirection] at hzero
    | some q =>
      cases t with
      | none =>
        simp [slopeDirection] at hzero
      | some r =>
        congr 1
        have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
        have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
        rw [← q.num_div_den, ← r.num_div_den, div_eq_div_iff hq hr]
        have hz : q.num * (r.den : ℤ) = (q.den : ℤ) * r.num := sub_eq_zero.mp hzero
        exact_mod_cast hz.trans (mul_comm (q.den : ℤ) r.num)
  have hExclude (c d : Curve S)
      (π : C(S,Circle)) (hπ : ∀ z, π (c.map z)=z)
      (r : Circle) (hd : ∀ z, π (d.map z)=r) :
      ¬ AmbientIsotopy.Rel c.image d.image := by
    have power_zero (k : ℤ)
        (h : (⟨fun z : Circle => z ^ k, continuous_zpow k⟩ : C(Circle, Circle)).Nullhomotopic) :
        k = 0 := by
      obtain ⟨r, ⟨H⟩⟩ := h
      obtain ⟨r₀, hr₀⟩ := Circle.exp_surjective r
      let G := H.symm
      let L : C(unitInterval × Circle, ℝ) := Circle.isCoveringMap_exp.liftHomotopy
        G.toContinuousMap (ContinuousMap.const Circle r₀)
        (fun z => (G.apply_zero z).trans hr₀.symm)
      have hL (t : unitInterval) (z : Circle) : Circle.exp (L (t, z)) = G (t, z) :=
        congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts G.toContinuousMap
          (ContinuousMap.const Circle r₀) _) (t, z)
      let F : C(Circle, ℝ) := ⟨fun z => L (1, z), L.continuous.comp
        (continuous_const.prodMk continuous_id)⟩
      have hF (z : Circle) : Circle.exp (F z) = z ^ k :=
        (hL 1 z).trans (G.apply_one z)
      let γ : C(unitInterval, Circle) :=
        ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      let δ : C(unitInterval, Circle) := ⟨fun t => (γ t) ^ k, (continuous_zpow k).comp γ.continuous⟩
      let Γ : C(unitInterval, ℝ) := F.comp γ
      let Λ : C(unitInterval, ℝ) := ⟨fun t => Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      have hΓlift : Circle.exp ∘ Γ = δ := by
        funext t
        exact hF (γ t)
      have hΛlift : Circle.exp ∘ Λ = δ := by
        funext t
        change Circle.exp (Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ))) = (γ t) ^ k
        rw [Circle.exp_add]
        have hΓ0 : Circle.exp (Γ 0) = 1 := by
          have hh := congrFun hΓlift 0
          simpa [δ, γ] using hh
        rw [hΓ0, one_mul]
        simpa only [zsmul_eq_mul, γ, ContinuousMap.coe_mk] using
          Circle.exp_zsmul (2 * Real.pi * (t : ℝ)) k
      have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
      have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
      have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
      have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
      have hloop : Γ 1 = Γ 0 := by
        change F (γ 1) = F (γ 0)
        congr 1
        simp [γ]
      rw [hloop] at hend
      have he : (k : ℝ) * (2 * Real.pi) = 0 := by
        have hh : Γ 0 = Γ 0 + (k : ℝ) * (2 * Real.pi) := by simpa [Λ] using hend
        linarith
      have hk : (k : ℝ) = 0 := (mul_eq_zero.mp he).resolve_right
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact_mod_cast hk
    have transfer {S : Type} [TopologicalSpace S] (c d : Curve S) (χ : C(S, Circle))
        (h : AmbientIsotopy.Rel c.image d.image)
        (hd : (χ.comp ⟨d.map, d.embedded.continuous⟩).Nullhomotopic) :
        (χ.comp ⟨c.map, c.embedded.continuous⟩).Nullhomotopic := by
      obtain ⟨H, hH⟩ := h
      have hr (z : Circle) : H.finalMap (c.map z) ∈ Set.range d.map := by
        rw [show Set.range d.map = d.image from rfl, ← hH]
        exact ⟨c.map z, ⟨z, rfl⟩, rfl⟩
      let η : C(Circle, Circle) := ⟨fun z => d.embedded.toHomeomorph.symm
        ⟨H.finalMap (c.map z), hr z⟩,
        d.embedded.toHomeomorph.symm.continuous.comp
          ((H.map.continuous.comp (continuous_const.prodMk c.embedded.continuous)).subtype_mk _)⟩
      have hη (z : Circle) : d.map (η z) = H.finalMap (c.map z) :=
        congrArg Subtype.val (d.embedded.toHomeomorph.apply_symm_apply
          ⟨H.finalMap (c.map z), hr z⟩)
      let G : (χ.comp ⟨c.map, c.embedded.continuous⟩).Homotopy
          ((χ.comp ⟨d.map, d.embedded.continuous⟩).comp η) := {
        toContinuousMap := ⟨fun tz => χ (H.map (tz.1, c.map tz.2)),
          χ.continuous.comp (H.map.continuous.comp
            (continuous_fst.prodMk (c.embedded.continuous.comp continuous_snd)))⟩
        map_zero_left := by
          intro z
          change χ (H.map (⟨0, by norm_num⟩, c.map z)) = χ (c.map z)
          rw [H.at_zero (c.map z)]
        map_one_left := by
          intro z
          change χ (H.finalMap (c.map z)) = χ (d.map (η z))
          rw [hη] }
      obtain ⟨r, hr⟩ := hd.comp_left η
      exact ⟨r, ContinuousMap.Homotopic.trans ⟨G⟩ hr⟩
    intro h
    have hdnull : (π.comp ⟨d.map,d.embedded.continuous⟩).Nullhomotopic := by
      have heq : π.comp ⟨d.map,d.embedded.continuous⟩=ContinuousMap.const Circle r := by
        apply ContinuousMap.ext
        intro z
        exact hd z
      rw [heq]
      exact ContinuousMap.nullhomotopic_of_constant r
    have hcnull := transfer c d π h hdnull
    have heq : π.comp ⟨c.map,c.embedded.continuous⟩=
        (⟨fun z : Circle => z^(1:ℤ),continuous_zpow _⟩ : C(Circle,Circle)) := by
      apply ContinuousMap.ext
      intro z
      simpa only [ContinuousMap.comp_apply,ContinuousMap.coe_mk,zpow_one] using hπ z
    rw [heq] at hcnull
    have hbad := power_zero 1 hcnull
    norm_num at hbad
  have hfamily (p : Torus) :
      ∃ (F : FareySlope → Curve (Punctured p)) (A : FareySlope → Torus),
        (∀ s z, ((F s).map z).val=A s*torusWindingMap (slopeDirection s).1 (slopeDirection s).2 z) ∧
        (∀ s, Admissible (F s)) ∧
        (∀ s, AmbientIsotopy.Rel (fill (F s)).image
          (range (torusWindingMap (slopeDirection s).1 (slopeDirection s).2))) ∧
        (∀ c : Curve (Punctured p), Admissible c →
          ∃! s, AmbientIsotopy.Rel c.image (F s).image) := by
    classical
    have produce (m n : ℤ) (hgcd : m.gcd n = 1) :
        ∃ (d : Curve (Punctured p)) (a : Torus),
          (∀ z, (d.map z).val=a*torusWindingMap m n z) ∧ Admissible d ∧
          AmbientIsotopy.Rel (fill d).image (range (torusWindingMap m n)) := by
      classical
      let u := Int.gcdA m n
      let v := Int.gcdB m n
      have hbez : m*u+n*v=1 := by
        have h := Int.gcd_eq_gcd_ab m n
        rw [hgcd] at h
        exact h.symm
      let a : Torus := (p.1 * (-1 : Circle)^(-v),p.2 * (-1 : Circle)^u)
      let χ : Torus → Circle := fun w => w.1^(-n)*w.2^m
      have hw (z : Circle) : χ (torusWindingMap m n z) = 1 := by
        dsimp [χ,torusWindingMap]
        rw [← zpow_mul,← zpow_mul,← zpow_add]
        rw [show m*(-n)+n*m=0 by ring]
        exact zpow_zero z
      have ha : χ a = χ p * (-1 : Circle) := by
        dsimp [χ,a]
        rw [mul_zpow,mul_zpow]
        rw [show (p.1 ^ (-n) * ((-1 : Circle)^(-v))^(-n)) *
            (p.2^m*((-1 : Circle)^u)^m) =
            (p.1^(-n)*p.2^m)*(((-1 : Circle)^(-v))^(-n)*((-1 : Circle)^u)^m) by ac_rfl]
        rw [← zpow_mul,← zpow_mul,← zpow_add]
        rw [show (-v)*(-n)+u*m=1 by nlinarith [hbez],zpow_one]
      have hχmul (x y : Torus) : χ (x*y)=χ x*χ y := by
        dsimp [χ]
        simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
        ac_rfl
      have avoids (z : Circle) : a*torusWindingMap m n z ≠ p := by
        intro he
        have hh := congrArg χ he
        rw [hχmul,hw,mul_one,ha] at hh
        have hn : (-1 : Circle)=1 := mul_left_cancel (hh.trans (mul_one _).symm)
        have hc := congrArg (fun z : Circle => (z : ℂ)) hn
        norm_num at hc
      let d : Curve (Punctured p) := {
        map := fun z => ⟨a*torusWindingMap m n z,avoids z⟩
        embedded := by
          apply (IsEmbedding.of_comp_iff (g := Subtype.val) IsEmbedding.subtypeVal).mp
          exact (Homeomorph.mulLeft a).isEmbedding.comp (torusWindingMap_isEmbedding hgcd)
      }
      have hd : Admissible d :=
        actual_translated_primitive_parameter_proves_essential (fill d) a m n hgcd (fun _ => rfl)
      let γ := PathConnectedSpace.somePath (1 : Torus) a
      let H : AmbientIsotopy Torus := {
        map := ⟨fun tx => γ tx.1 * tx.2,by fun_prop⟩
        homeomorphism_at := fun t => ⟨Homeomorph.mulLeft (γ t),fun _ => rfl⟩
        at_zero := by intro x; simp [γ]
      }
      have hh : H.finalMap '' range (torusWindingMap m n) = (fill d).image := by
        change (fun x => γ 1 * x) '' range (torusWindingMap m n) = range (fun z => a*torusWindingMap m n z)
        rw [γ.target]
        exact (range_comp _ _).symm
      exact ⟨d,a,fun _ => rfl,hd,ambientIsotopy_equivalence.symm ⟨H,hh⟩⟩
    have hs (s : FareySlope) : (slopeDirection s).1.gcd (slopeDirection s).2=1 := by
      cases s with
      | none => decide
      | some q => exact rationalSlope_primitive q
    choose F A hParam hAdm hRef using (fun s => produce (slopeDirection s).1 (slopeDirection s).2 (hs s))
    refine ⟨F,A,hParam,hAdm,hRef,?_⟩
    exact admissible_punctured_classification p F hRef
  obtain ⟨eU⟩ := hTU
  have hCompactLocalized (a b : Curve (Punctured (1,1)))
      (h : AmbientIsotopy.Rel a.image b.image) :
      ∃ (H : AmbientIsotopy (Punctured (1,1))) (K : Set (Punctured (1,1))),
        IsCompact K ∧ (∀ t x, x∉K → H.map (t,x)=x) ∧ H.finalMap '' a.image=b.image := by
    have hAssemble {S : Type} [TopologicalSpace S] (F : CurveComplex.Interval → Set S)
        (hlocal : ∀ t, ∃ V : Set CurveComplex.Interval, IsOpen V ∧ t ∈ V ∧
          ∀ s ∈ V, ∃ (H : AmbientIsotopy S) (K : Set S), IsCompact K ∧
            (∀ u x, x ∉ K → H.map (u,x)=x) ∧ H.finalMap '' F t=F s) :
        ∃ (H : AmbientIsotopy S) (K : Set S), IsCompact K ∧
          (∀ u x, x ∉ K → H.map (u,x)=x) ∧ H.finalMap '' F 0=F 1 := by
      let R : Set S → Set S → Prop := fun a b =>
        ∃ (H : AmbientIsotopy S) (K : Set S), IsCompact K ∧
          (∀ u x, x ∉ K → H.map (u,x)=x) ∧ H.finalMap '' a=b
      have hrefl (a : Set S) : R a a := by
        refine ⟨AmbientIsotopy.identity S,∅,isCompact_empty,fun u x hx => rfl,?_⟩
        exact Set.image_id a
      have htrans (a b c : Set S) (hab : R a b) (hbc : R b c) : R a c := by
        obtain ⟨H,K,hK,hfix,hH⟩ := hab
        obtain ⟨J,L,hL,hfixJ,hJ⟩ := hbc
        refine ⟨H.compose J,K ∪ L,hK.union hL,?_,?_⟩
        · intro u x hx
          change J.map (u,H.map (u,x))=x
          rw [hfix u x (fun h => hx (Or.inl h))]
          exact hfixJ u x (fun h => hx (Or.inr h))
        · rw [AmbientIsotopy.compose_finalMap,Set.image_comp,hH,hJ]
      have hsymm (a b : Set S) (hab : R a b) : R b a := by
        obtain ⟨H,K,hK,hfix,hH⟩ := hab
        obtain ⟨e,he⟩ := H.homeomorphism_at 1
        let reverse : CurveComplex.Interval → CurveComplex.Interval := fun t =>
          ⟨1-t.val,by constructor <;> linarith [t.property.1,t.property.2]⟩
        have hreverse : Continuous reverse :=
          (continuous_const.sub continuous_subtype_val).subtype_mk _
        have hr0 : reverse 0=1 := Subtype.ext (by norm_num [reverse])
        have hr1 : reverse 1=0 := Subtype.ext (by norm_num [reverse])
        let J : AmbientIsotopy S := {
          map := ⟨fun q => H.map (reverse q.1,e.symm q.2),
            H.map.continuous.comp ((hreverse.comp continuous_fst).prodMk
              (e.symm.continuous.comp continuous_snd))⟩
          homeomorphism_at := by
            intro t
            obtain ⟨g,hg⟩ := H.homeomorphism_at (reverse t)
            exact ⟨e.symm.trans g,fun x => by
              simpa [Homeomorph.trans_apply] using hg (e.symm x)⟩
          at_zero := by
            intro x
            change H.map (reverse 0,e.symm x)=x
            rw [hr0,← he,e.apply_symm_apply] }
        refine ⟨J,K,hK,?_,?_⟩
        · intro t x hx
          have hefix : e x=x := (he x).trans (hfix 1 x hx)
          have hinv : e.symm x=x :=
            (congrArg e.symm hefix.symm).trans (e.symm_apply_apply x)
          change H.map (reverse t,e.symm x)=x
          rw [hinv]
          exact hfix _ x hx
        · have hfinal : J.finalMap = e.symm := by
            funext x
            change H.map (reverse 1,e.symm x)=e.symm x
            rw [hr1]
            exact H.at_zero _
          have himage : e '' a=b := by
            have hefinal : (e : S → S)=H.finalMap := funext he
            rw [hefinal]
            exact hH
          rw [hfinal,← himage]
          simp [Set.image_image]
      let A : Set CurveComplex.Interval := {t | R (F 0) (F t)}
      have hAo : IsOpen A := by
        apply isOpen_iff_mem_nhds.mpr
        intro t ht
        obtain ⟨V,hV,htV,hVs⟩ := hlocal t
        apply Filter.mem_of_superset (hV.mem_nhds htV)
        intro s hs
        exact htrans _ _ _ ht (hVs s hs)
      have hAc : IsOpen Aᶜ := by
        apply isOpen_iff_mem_nhds.mpr
        intro t ht
        obtain ⟨V,hV,htV,hVs⟩ := hlocal t
        apply Filter.mem_of_superset (hV.mem_nhds htV)
        intro s hs hsa
        exact ht (htrans _ _ _ hsa (hsymm _ _ (hVs s hs)))
      have hAU : A=Set.univ :=
        IsClopen.eq_univ ⟨by simpa using hAc.isClosed_compl,hAo⟩ ⟨0,hrefl (F 0)⟩
      have hOne : (1 : CurveComplex.Interval) ∈ A := by rw [hAU];trivial
      exact hOne
    have hModelBridge {X : Type} [TopologicalSpace X] [T2Space X]
        (F : C(CurveComplex.Interval × Circle,X))
        (hF : ∀ t : CurveComplex.Interval, IsEmbedding (fun z => F (t,z)))
        (t : CurveComplex.Interval)
        (e : C(Set.Ioo (-1 : ℝ) 1 × Circle,X)) (he : IsOpenEmbedding e)
        (hcenter : ∀ z, e (⟨0,by norm_num⟩,z)=F (t,z)) :
        ∃ V : Set CurveComplex.Interval, IsOpen V ∧ t ∈ V ∧
          ∀ s ∈ V, ∃ (H : AmbientIsotopy X) (K : Set X), IsCompact K ∧
            (∀ u x, x ∉ K → H.map (u,x)=x) ∧
            H.finalMap '' Set.range (fun z => F (t,z))=Set.range (fun z => F (s,z)) := by
      classical
      let E := he.isEmbedding.toHomeomorph
      let width : CurveComplex.Interval → Set.Ioo (-1 : ℝ) 1 := fun u =>
        ⟨u.val-1/2,by constructor <;> linarith [u.property.1,u.property.2]⟩
      have hwc : Continuous width := (continuous_subtype_val.sub continuous_const).subtype_mk _
      let B : C(Circle × CurveComplex.Interval,X) :=
        ⟨fun q => e (width q.2,q.1),
          e.continuous.comp ((hwc.comp continuous_snd).prodMk continuous_fst)⟩
      have hBi : Function.Injective B := by
        rintro ⟨z,u⟩ ⟨w,v⟩ hh
        have hh' := he.injective hh
        have hz : z=w := congrArg Prod.snd hh'
        have huv := congrArg (fun q : Set.Ioo (-1 : ℝ) 1 × Circle => q.1.val) hh'
        have hu : u=v := by apply Subtype.ext;dsimp [width] at huv;linarith
        exact Prod.ext hz hu
      have hB : IsEmbedding B := (B.continuous.isClosedEmbedding hBi).isEmbedding
      let W : Set (Set.Ioo (-1 : ℝ) 1 × Circle) :=
        {q | -(1/2 : ℝ)<q.1.val ∧ q.1.val<1/2}
      let U : Set X := e '' W
      have hWo : IsOpen W := isOpen_Ioo.preimage
        (continuous_subtype_val.comp continuous_fst)
      have hU : IsOpen U := he.isOpenMap W hWo
      have hBt (z : Circle) : B (z,⟨1/2,by norm_num⟩)=F (t,z) := by
        change e (width ⟨1/2,by norm_num⟩,z)=F (t,z)
        have hwidth : width ⟨1/2,by norm_num⟩=⟨0,by norm_num⟩ := Subtype.ext (by norm_num [width])
        rw [hwidth,hcenter]
      have hBint (q : Circle × CurveComplex.Interval) (hq0 : 0<q.2) (hq1 : q.2<1) : B q ∈ U := by
        refine ⟨(width q.2,q.1),?_,rfl⟩
        change -(1/2 : ℝ)<q.2.val-1/2 ∧ q.2.val-1/2<1/2
        have h0 : 0<q.2.val := hq0
        have h1 : q.2.val<1 := hq1
        constructor <;> linarith
      have hUA : U ⊆ Set.range B := by
        rintro x ⟨q,hq,rfl⟩
        let u : CurveComplex.Interval := ⟨q.1.val+1/2,by
          change -(1/2 : ℝ)<q.1.val ∧ q.1.val<1/2 at hq
          constructor <;> linarith [hq.1,hq.2]⟩
        refine ⟨(q.2,u),?_⟩
        change e (width u,q.2)=e q
        congr 1
        refine Prod.ext ?_ rfl
        apply Subtype.ext
        dsimp [width,u]
        ring
      have hFtU : ∀ z, F (t,z) ∈ U := by
        intro z
        rw [← hcenter]
        exact ⟨(⟨0,by norm_num⟩,z),by norm_num [W],rfl⟩
      have hsub : ({t} : Set CurveComplex.Interval) ×ˢ (Set.univ : Set Circle) ⊆ F ⁻¹' U := by
        rintro ⟨v,z⟩ ⟨hv,hz⟩
        have hvt : v=t := Set.mem_singleton_iff.mp hv
        subst v
        exact hFtU z
      obtain ⟨V,Q,hV,hQ,htV,hQall,hVQ⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_univ
          (hU.preimage F.continuous) hsub
      have htV' : t ∈ V := htV (Set.mem_singleton t)
      obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV t htV'
      refine ⟨Metric.ball t η,Metric.isOpen_ball,Metric.mem_ball_self hη,?_⟩
      intro s hs
      let α : CurveComplex.Interval → CurveComplex.Interval := fun u =>
        ⟨(1-u.val)*t.val+u.val*s.val,by
          constructor
          · exact add_nonneg (mul_nonneg (sub_nonneg.mpr u.property.2) t.property.1)
              (mul_nonneg u.property.1 s.property.1)
          · nlinarith [mul_nonneg (sub_nonneg.mpr u.property.2) (sub_nonneg.mpr t.property.2),
              mul_nonneg u.property.1 (sub_nonneg.mpr s.property.2)]⟩
      have hαc : Continuous α := by dsimp [α];fun_prop
      have hα0 : α 0=t := Subtype.ext (by simp [α])
      have hα1 : α 1=s := Subtype.ext (by simp [α])
      have hαV (u : CurveComplex.Interval) : α u ∈ V := by
        apply hηV
        have hst : |s.val-t.val|<η := hs
        change |((1-u.val)*t.val+u.val*s.val)-t.val|<η
        rw [show ((1-u.val)*t.val+u.val*s.val)-t.val=u.val*(s.val-t.val) by ring,
          abs_mul,abs_of_nonneg u.property.1]
        calc
          u.val*|s.val-t.val| ≤ 1*|s.val-t.val| :=
            mul_le_mul_of_nonneg_right u.property.2 (abs_nonneg _)
          _ < η := by simpa using hst
      have hFU (u : CurveComplex.Interval) (z : Circle) : F (α u,z) ∈ U :=
        hVQ ⟨hαV u,hQall (Set.mem_univ z)⟩
      have hFrange (u : CurveComplex.Interval) (z : Circle) : F (α u,z) ∈ Set.range e := by
        obtain ⟨q,hq,heq⟩ := hFU u z
        exact ⟨q,heq⟩
      let C : C(CurveComplex.Interval × Circle,Set.Ioo (-1 : ℝ) 1 × Circle) :=
        ⟨fun q => E.symm ⟨F (α q.1,q.2),hFrange q.1 q.2⟩,
          E.symm.continuous.comp ((F.continuous.comp
            ((hαc.comp continuous_fst).prodMk continuous_snd)).subtype_mk _)⟩
      have hCe (u : CurveComplex.Interval) (z : Circle) : e (C (u,z))=F (α u,z) :=
        congrArg Subtype.val (E.apply_symm_apply ⟨F (α u,z),hFrange u z⟩)
      have hCW (u : CurveComplex.Interval) (z : Circle) : C (u,z) ∈ W := by
        obtain ⟨q,hq,heq⟩ := hFU u z
        have hh : C (u,z)=q := he.injective ((hCe u z).trans heq.symm)
        rw [hh]
        exact hq
      have hCbound (u : CurveComplex.Interval) (z : Circle) :
          0 < (C (u,z)).1.val+1/2 ∧ (C (u,z)).1.val+1/2 < 1 := by
        have hh := hCW u z
        change -(1/2 : ℝ)<(C (u,z)).1.val ∧ (C (u,z)).1.val<1/2 at hh
        constructor <;> linarith [hh.1,hh.2]
      let G : C(CurveComplex.Interval × Circle,Circle × CurveComplex.Interval) :=
        ⟨fun q => ((C q).2,⟨(C q).1.val+1/2,
          ⟨(hCbound q.1 q.2).1.le,(hCbound q.1 q.2).2.le⟩⟩),
          (continuous_snd.comp C.continuous).prodMk
            (((continuous_subtype_val.comp (continuous_fst.comp C.continuous)).add continuous_const).subtype_mk _)⟩
      have hBG (u : CurveComplex.Interval) (z : Circle) : B (G (u,z))=F (α u,z) := by
        change e (width (G (u,z)).2,(G (u,z)).1)=F (α u,z)
        have hh : (width (G (u,z)).2,(G (u,z)).1)=C (u,z) := by
          refine Prod.ext ?_ rfl
          apply Subtype.ext
          dsimp [width,G]
          ring
        rw [hh,hCe]
      have hGe (u : CurveComplex.Interval) : IsEmbedding (fun z => G (u,z)) := by
        have hc : Continuous (fun z => G (u,z)) :=
          G.continuous.comp (continuous_const.prodMk continuous_id)
        have heq : (B ∘ fun z => G (u,z))=(fun z => F (α u,z)) := funext (hBG u)
        apply IsEmbedding.of_comp hc B.continuous
        rw [heq]
        exact hF (α u)
      have hGint (u : CurveComplex.Interval) (z : Circle) :
          G (u,z) ∈ Set.univ ×ˢ Set.Ioo (0 : CurveComplex.Interval) 1 :=
        ⟨Set.mem_univ _,(hCbound u z).1,(hCbound u z).2⟩
      have hG0 (z : Circle) : G (0,z)=(z,⟨1/2,by norm_num⟩) := by
        have hC0 : C (0,z)=(⟨0,by norm_num⟩,z) := by
          apply he.injective
          rw [hCe,hα0,hcenter]
        apply Prod.ext
        · change (C (0,z)).2=z
          rw [hC0]
        · apply Subtype.ext
          change (C (0,z)).1.val+1/2=1/2
          simp [hC0]
      obtain ⟨L,hL0,hL1,hLfinal⟩ :=
        SDRModelAnnulusReview.actual_model_annulus_embedded_circle_family_boundary_fixed_endpoint_extension
          G hGe hGint hG0
      -- Joint inverse and compact embedding extension are actual source transport.
      have hInverse {Y : Type} [TopologicalSpace Y] [CompactSpace Y] [T2Space Y]
          (H : AmbientIsotopy Y) : ∃ J : C(CurveComplex.Interval × Y,Y),
            (∀ u y, J (u,H.map (u,y))=y) ∧ (∀ u y, H.map (u,J (u,y))=y) := by
        let T : CurveComplex.Interval × Y → CurveComplex.Interval × Y :=
          fun q => (q.1,H.map q)
        have hc : Continuous T := continuous_fst.prodMk H.map.continuous
        have hi : Function.Injective T := by
          rintro ⟨t,x⟩ ⟨s,y⟩ hh
          have ht : t=s := congrArg Prod.fst hh
          subst s
          obtain ⟨e,he⟩ := H.homeomorphism_at t
          have hxy : e x=e y := by
            rw [he,he]
            exact congrArg Prod.snd hh
          exact Prod.ext rfl (e.injective hxy)
        have hs : Function.Surjective T := by
          rintro ⟨t,y⟩
          obtain ⟨e,he⟩ := H.homeomorphism_at t
          refine ⟨(t,e.symm y),Prod.ext rfl ?_⟩
          change H.map (t,e.symm y)=y
          rw [← he,e.apply_symm_apply]
        obtain ⟨P,hP⟩ := isHomeomorph_iff_exists_homeomorph.mp
          ((isHomeomorph_iff_continuous_bijective).mpr ⟨hc,hi,hs⟩)
        have htime (q : CurveComplex.Interval × Y) : (P.symm q).1=q.1 := by
          have hh := congrArg Prod.fst (P.apply_symm_apply q)
          rw [congrFun hP] at hh
          exact hh
        let J : C(CurveComplex.Interval × Y,Y) :=
          ⟨fun q => (P.symm q).2,continuous_snd.comp P.symm.continuous⟩
        refine ⟨J,?_,?_⟩
        · intro t y
          have hh := congrArg Prod.snd (P.symm_apply_apply (t,y))
          rw [congrFun hP] at hh
          exact hh
        · intro t y
          have hh := congrArg Prod.snd (P.apply_symm_apply (t,y))
          rw [congrFun hP] at hh
          have he : P.symm (t,y)=(t,J (t,y)) := Prod.ext (htime _) rfl
          rw [he] at hh
          exact hh
      obtain ⟨J,hJleft,hJright⟩ := hInverse L
      have hfix (u : CurveComplex.Interval) (q : Circle × CurveComplex.Interval)
          (hq : B q ∉ U) : L.map (u,q)=q := by
        have hb : q.2=0 ∨ q.2=1 := by
          by_contra h
          push_neg at h
          exact hq (hBint q (lt_of_le_of_ne q.2.property.1 h.1.symm)
            (lt_of_le_of_ne q.2.property.2 h.2))
        rcases hb with hb | hb
        · rw [show q=(q.1,0) from Prod.ext rfl hb,hL0]
        · rw [show q=(q.1,1) from Prod.ext rfl hb,hL1]
      obtain ⟨H,A,hH,hHfix,hAleft,hAright⟩ :=
        G3Review.actual_compact_embedded_motion_extension B hB U hU hUA L J hJleft hJright hfix
      refine ⟨H,Set.range B,isCompact_range B.continuous,?_,?_⟩
      · intro u x hx
        exact hHfix u x (fun hu => hx (hUA hu))
      · have hcomm : H.finalMap ∘ B=B ∘ L.finalMap := funext (hH 1)
        have hcore : Set.range (fun z => B (z,⟨1/2,by norm_num⟩))=
            Set.range (fun z => F (t,z)) := by congr 1;funext z;exact hBt z
        have hlast : Set.range (fun z => B (G (1,z)))=Set.range (fun z => F (s,z)) := by
          congr 1
          funext z
          rw [hBG,hα1]
        have hcoreimg : B '' Set.range (fun z : Circle =>
            (z,(⟨1/2,by norm_num⟩ : CurveComplex.Interval)))=
            Set.range (fun z => F (t,z)) := by
          simpa only [← Set.range_comp,Function.comp_def] using hcore
        have hlastimg : B '' Set.range (fun z => G (1,z))=
            Set.range (fun z => F (s,z)) := by
          simpa only [← Set.range_comp,Function.comp_def] using hlast
        rw [← hcoreimg,← Set.image_comp,hcomm,Set.image_comp,hLfinal]
        exact hlastimg
    have hSourceCollar (S : Type) [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
        (U : Set S) (hU : IsOpen U) (p : Torus) (a : U ≃ₜ Punctured p)
        (b : Curve (Punctured p)) :
        ∃ e : C(Set.Ioo (-1 : ℝ) 1 × Circle,Punctured p),
          IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z)=b.map z := by
      letI : ClosedSurface S := Classical.choice hS.2.1
      let c : Curve S := ⟨fun z => (a.symm (b.map z)).val,
        IsEmbedding.subtypeVal.comp (a.symm.isEmbedding.comp b.embedded)⟩
      have hcollar : ∃ e : C(Set.Ioo (-1 : ℝ) 1 × Circle,S),
          IsOpenEmbedding e ∧ ∀ z, e (⟨0,by norm_num⟩,z)=c.map z := by
        rcases LocalSurgery.embedded_circle_annular_collar_or_local_reflection S c with
          h | ⟨x,⟨W⟩⟩
        · exact h
        · exact False.elim (GenusOrientationCandidate.no_local_reflection_witness
            2 hS x (GenusOrientationCandidate.surface_puncture_homologyInclusion_zero x) W)
      obtain ⟨e,he,hcenter⟩ := hcollar
      let zero : Set.Ioo (-1 : ℝ) 1 := ⟨0,by norm_num⟩
      have hsub : ({zero} : Set (Set.Ioo (-1 : ℝ) 1)) ×ˢ (Set.univ : Set Circle) ⊆ e ⁻¹' U := by
        rintro ⟨w,z⟩ ⟨hw,hz⟩
        have hw0 : w=zero := Set.mem_singleton_iff.mp hw
        subst w
        change e (⟨0,by norm_num⟩,z) ∈ U
        rw [hcenter]
        exact (a.symm (b.map z)).property
      obtain ⟨V,Q,hV,hQ,hzeroV,hQall,hVQ⟩ :=
        generalized_tube_lemma isCompact_singleton isCompact_univ
          (hU.preimage e.continuous) hsub
      obtain ⟨η,hη,hηV⟩ := Metric.isOpen_iff.mp hV zero (hzeroV (Set.mem_singleton zero))
      let δ : ℝ := min (η/2) (1/2)
      have hδ : 0<δ := lt_min (half_pos hη) (by norm_num)
      have hδ1 : δ<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
      have hδη : δ<η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      let scale : Set.Ioo (-1 : ℝ) 1 → Set.Ioo (-1 : ℝ) 1 := fun w =>
        ⟨δ*w.val,by
          have ha : |δ*w.val|<1 := by
            rw [abs_mul,abs_of_pos hδ]
            have hw : |w.val|<1 := abs_lt.mpr w.property
            exact (mul_lt_mul_of_pos_left hw hδ).trans (by simpa using hδ1)
          exact abs_lt.mp ha⟩
      let k : Set.Ioo (-1 : ℝ) 1 × Circle → Set.Ioo (-1 : ℝ) 1 × Circle :=
        fun q => (scale q.1,q.2)
      have hk : IsOpenEmbedding k := by
        let j : Set.Ioo (-1 : ℝ) 1 × Circle → ℝ × Circle := fun q => (q.1.val,q.2)
        have hj : IsOpenEmbedding j :=
          isOpen_Ioo.isOpenEmbedding_subtypeVal.prodMap IsOpenEmbedding.id
        let L : (ℝ × Circle) ≃ₜ (ℝ × Circle) :=
          (Homeomorph.mulLeft₀ δ hδ.ne').prodCongr (Homeomorph.refl Circle)
        have hcomp : IsOpenEmbedding (j ∘ k) := by
          have hh : j ∘ k=L ∘ j := rfl
          rw [hh]
          exact L.isOpenEmbedding.comp hj
        exact IsOpenEmbedding.of_comp k hj hcomp
      have hkU (q : Set.Ioo (-1 : ℝ) 1 × Circle) : e (k q) ∈ U := by
        apply hVQ
        refine ⟨hηV ?_,hQall (Set.mem_univ _)⟩
        change |δ*q.1.val-0|<η
        rw [sub_zero,abs_mul,abs_of_pos hδ]
        have hw : |q.1.val|<1 := abs_lt.mpr q.1.property
        exact (mul_lt_mul_of_pos_left hw hδ).trans (by simpa using hδη)
      let g : C(Set.Ioo (-1 : ℝ) 1 × Circle,U) :=
        ⟨fun q => ⟨e (k q),hkU q⟩,
          (e.continuous.comp hk.continuous).subtype_mk _⟩
      have hg : IsOpenEmbedding g :=
        IsOpenEmbedding.of_comp g hU.isOpenEmbedding_subtypeVal (he.comp hk)
      let f : C(Set.Ioo (-1 : ℝ) 1 × Circle,Punctured p) :=
        ⟨fun q => a (g q),a.continuous.comp g.continuous⟩
      refine ⟨f,a.isOpenEmbedding.comp hg,?_⟩
      intro z
      have hk0 : k (zero,z)=(zero,z) := by
        refine Prod.ext ?_ rfl
        apply Subtype.ext
        change δ*0=0
        ring
      have hg0 : g (zero,z)=a.symm (b.map z) := by
        apply Subtype.ext
        change e (k (zero,z))=(a.symm (b.map z)).val
        rw [hk0,hcenter]
      change a (g (zero,z))=b.map z
      rw [hg0,a.apply_symm_apply]
    obtain ⟨H,hH⟩ := h
    let T : C(CurveComplex.Interval × Circle,Punctured (1,1)) :=
      ⟨fun q => H.map (q.1,a.map q.2),H.map.continuous.comp
        (continuous_fst.prodMk (a.embedded.continuous.comp continuous_snd))⟩
    have hTe (t : CurveComplex.Interval) : IsEmbedding (fun z => T (t,z)) := by
      obtain ⟨f,hf⟩ := H.homeomorphism_at t
      have heq : (fun z => T (t,z))=f ∘ a.map := funext (fun z => (hf _).symm)
      rw [heq]
      exact f.isEmbedding.comp a.embedded
    have hLocal : ∀ t : CurveComplex.Interval,
        ∃ W : Set CurveComplex.Interval, IsOpen W ∧ t ∈ W ∧
          ∀ s ∈ W, ∃ (J : AmbientIsotopy (Punctured (1,1))) (K : Set (Punctured (1,1))),
            IsCompact K ∧ (∀ u x, x ∉ K → J.map (u,x)=x) ∧
            J.finalMap '' Set.range (fun z => T (t,z))=Set.range (fun z => T (s,z)) := by
      intro t
      let d : Curve (Punctured (1,1)) := ⟨fun z => T (t,z),hTe t⟩
      obtain ⟨e,he,hcenter⟩ := hSourceCollar S hS U hU (1,1) eU d
      exact hModelBridge T hTe t e he hcenter
    obtain ⟨J,K,hK,hfix,hJ⟩ := hAssemble (fun t => Set.range (fun z => T (t,z))) hLocal
    have hzero : Set.range (fun z => T (0,z))=a.image := by
      change Set.range (fun z => H.map (0,a.map z))=Set.range a.map
      congr 1
      funext z
      exact H.at_zero _
    have hone : Set.range (fun z => T (1,z))=b.image := by
      rw [← hH]
      change Set.range (H.finalMap ∘ a.map)=H.finalMap '' Set.range a.map
      exact Set.range_comp H.finalMap a.map
    rw [hzero,hone] at hJ
    exact ⟨J,K,hK,hfix,hJ⟩
  obtain ⟨eV⟩ := hTV
  obtain ⟨F,A,hParam,hAdm,hRef,hClass⟩ := hfamily (1,1)
  let GU : FareySlope → Curve S := fun s => {
    map := fun z => (eU.symm ((F s).map z)).val
    embedded := _root_.Topology.IsEmbedding.subtypeVal.comp
      (eU.symm.isEmbedding.comp (F s).embedded)
  }
  let GV : FareySlope → Curve S := fun s => {
    map := fun z => (eV.symm ((F s).map z)).val
    embedded := _root_.Topology.IsEmbedding.subtypeVal.comp
      (eV.symm.isEmbedding.comp (F s).embedded)
  }
  have hPrimitive (s : FareySlope) : (slopeDirection s).1.gcd (slopeDirection s).2=1 := by
    cases s with
    | none => decide
    | some q => exact rationalSlope_primitive q
  have hDerivedU (s : FareySlope) : Essential (GU s) ∧ Nonseparating (GU s) := by
    apply hSideEssential U hU (1,1) eU (GU s) (A s)
      (slopeDirection s).1 (slopeDirection s).2 (hPrimitive s)
    intro z
    refine ⟨eU.symm ((F s).map z),rfl,?_⟩
    rw [eU.apply_symm_apply]
    exact hParam s z
  have hDerivedV (s : FareySlope) : Essential (GV s) ∧ Nonseparating (GV s) := by
    apply hSideEssential V hV (1,1) eV (GV s) (A s)
      (slopeDirection s).1 (slopeDirection s).2 (hPrimitive s)
    intro z
    refine ⟨eV.symm ((F s).map z),rfl,?_⟩
    rw [eV.apply_symm_apply]
    exact hParam s z
  have hEssU (s : FareySlope) : Essential (GU s) := (hDerivedU s).1
  have hEssV (s : FareySlope) : Essential (GV s) := (hDerivedV s).1
  let vertex : Sum FareySlope FareySlope → Vertex S := fun slope =>
    match slope with
    | .inl s => Quotient.mk (essentialCurveSetoid S) ⟨GU s,hEssU s⟩
    | .inr s => Quotient.mk (essentialCurveSetoid S) ⟨GV s,hEssV s⟩
  have hGU : ∀ s, (GU s).image ⊆ U := by
    intro s x hx
    obtain ⟨z,rfl⟩ := hx
    exact (eU.symm ((F s).map z)).property
  have hGV : ∀ s, (GV s).image ⊆ V := by
    intro s x hx
    obtain ⟨z,rfl⟩ := hx
    exact (eV.symm ((F s).map z)).property
  have hSideContacts (S : Type) [TopologicalSpace S] (U : Set S) (p₀ : Torus)
      (e : U ≃ₜ Punctured p₀) (c d : Curve S)
      (a b : Torus) (m n p q : ℤ)
      (hc : ∀ z, c.map z ∈ U) (hd : ∀ z, d.map z ∈ U)
      (hpc : ∀ z, (e ⟨c.map z,hc z⟩).val=a*torusWindingMap m n z)
      (hpd : ∀ z, (e ⟨d.map z,hd z⟩).val=b*torusWindingMap p q z)
      (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
      (c.image ∩ d.image).Subsingleton := by
    have hContacts (a b : Torus) (m n p q : ℤ) (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
        (range (fun z => a*torusWindingMap m n z) ∩
          range (fun z => b*torusWindingMap p q z)).Subsingleton := by
      let χ : Torus → Circle := fun x => x.1^(-n)*x.2^m
      have hmul (x y : Torus) : χ (x*y)=χ x*χ y := by
        dsimp [χ]
        simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
        ac_rfl
      have hwind (u v : ℤ) (z : Circle) : χ (torusWindingMap u v z)=z^(u*(-n)+v*m) := by
        dsimp [χ,torusWindingMap]
        rw [←zpow_mul,←zpow_mul,←zpow_add]
      have hzero (z : Circle) : χ (a*torusWindingMap m n z)=χ a := by
        rw [hmul,hwind,show m*(-n)+n*m=0 by ring,zpow_zero,mul_one]
      intro x hx y hy
      obtain ⟨z,hz⟩ := hx.1
      obtain ⟨w,hw⟩ := hx.2
      obtain ⟨z',hz'⟩ := hy.1
      obtain ⟨w',hw'⟩ := hy.2
      have he : χ x=χ y := by rw [←hz,←hz',hzero,hzero]
      rw [←hw,←hw',hmul,hmul,hwind,hwind] at he
      have hp := mul_left_cancel he
      have hexp : p*(-n)+q*m=m*q-n*p := by ring
      rw [hexp] at hp
      have hww : w=w' := by
        rcases hdet with hdet|hdet
        · simpa only [hdet,zpow_one] using hp
        · have hi : w⁻¹=w'⁻¹ := by simpa only [hdet,zpow_neg_one] using hp
          exact inv_injective hi
      rw [←hw,←hw',hww]
    intro x hx y hy
    obtain ⟨z,hz⟩ := hx.1
    obtain ⟨w,hw⟩ := hx.2
    obtain ⟨z',hz'⟩ := hy.1
    obtain ⟨w',hw'⟩ := hy.2
    have hxU : x ∈ U := hz ▸ hc z
    have hyU : y ∈ U := hz' ▸ hc z'
    have hval : (e ⟨x,hxU⟩).val=(e ⟨y,hyU⟩).val := by
      apply hContacts a b m n p q hdet
      · constructor
        · exact ⟨z,by simpa only [hz] using (hpc z).symm⟩
        · exact ⟨w,by simpa only [hw] using (hpd w).symm⟩
      · constructor
        · exact ⟨z',by simpa only [hz'] using (hpc z').symm⟩
        · exact ⟨w',by simpa only [hw'] using (hpd w').symm⟩
    exact congrArg Subtype.val (e.injective (Subtype.ext hval))
  have hContactU (s t : FareySlope)
      (hdet : (slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1=1 ∨
        (slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1 = -1) :
      ((GU s).image ∩ (GU t).image).Subsingleton := by
    apply hSideContacts S U (1,1) eU (GU s) (GU t) (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (fun z => hGU s (mem_range_self z)) (fun z => hGU t (mem_range_self z))
    · intro z
      change (eU (eU.symm ((F s).map z))).val=_
      rw [eU.apply_symm_apply]
      exact hParam s z
    · intro z
      change (eU (eU.symm ((F t).map z))).val=_
      rw [eU.apply_symm_apply]
      exact hParam t z
    · exact hdet
  have hContactV (s t : FareySlope)
      (hdet : (slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1=1 ∨
        (slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1 = -1) :
      ((GV s).image ∩ (GV t).image).Subsingleton := by
    apply hSideContacts S V (1,1) eV (GV s) (GV t) (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (fun z => hGV s (mem_range_self z)) (fun z => hGV t (mem_range_self z))
    · intro z
      change (eV (eV.symm ((F s).map z))).val=_
      rw [eV.apply_symm_apply]
      exact hParam s z
    · intro z
      change (eV (eV.symm ((F t).map z))).val=_
      rw [eV.apply_symm_apply]
      exact hParam t z
    · exact hdet
  have hSideUpper (S : Type) [TopologicalSpace S] (U : Set S) (hU : IsOpen U)
      (p₀ : Torus) (e : U ≃ₜ Punctured p₀)
      (a b : Curve (Punctured p₀)) (c d : EssentialCurve S)
      (A B : Torus) (m n p q : ℤ) (hg : m.gcd n=1) (hg' : p.gcd q=1)
      (ha : ∀ z, (a.map z).val=A*torusWindingMap m n z)
      (hb : ∀ z, (b.map z).val=B*torusWindingMap p q z)
      (hc : ∀ z, (e.symm (a.map z)).val=c.val.map z)
      (hd : ∀ z, (e.symm (b.map z)).val=d.val.map z)
      (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
      geometricIntersection (Quotient.mk (essentialCurveSetoid S) c)
        (Quotient.mk (essentialCurveSetoid S) d) ≤ 1 := by
    have hTorus (c d : Curve Torus) (a b : Torus) (m n p q : ℤ)
        (hg : m.gcd n=1) (hg' : p.gcd q=1) (hdet : m*q-n*p=1)
        (hc : ∀ z, c.map z=a*torusWindingMap m n z)
        (hd : ∀ z, d.map z=b*torusWindingMap p q z) : Transverse c d := by
      have hFiber (a : Torus) (m n : ℤ) (hgcd : m.gcd n=1) :
          range (fun z => a*torusWindingMap m n z) =
            {x | x.1^(-n)*x.2^m=a.1^(-n)*a.2^m} := by
        let u := Int.gcdA m n
        let v := Int.gcdB m n
        have hbez : m*u+n*v=1 := by
          have h := Int.gcd_eq_gcd_ab m n
          rw [hgcd] at h
          exact h.symm
        let e := actual_integer_basis_torus_homeomorph m n u v hbez
        let χ : Torus → Circle := fun x => x.1^(-n)*x.2^m
        have hmul (x y : Torus) : χ (x*y)=χ x*χ y := by
          dsimp [χ]
          simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
          ac_rfl
        have hw (z : Circle) : e (torusWindingMap m n z)=(z,1) := by
          apply Prod.ext
          · change (z^m)^u*(z^n)^v=z
            rw [←zpow_mul,←zpow_mul,←zpow_add,hbez,zpow_one]
          · change (z^m)^(-n)*(z^n)^m=1
            rw [←zpow_mul,←zpow_mul,←zpow_add,show m*(-n)+n*m=0 by ring,zpow_zero]
        ext x
        constructor
        · rintro ⟨z,rfl⟩
          change χ (a*torusWindingMap m n z)=χ a
          rw [hmul]
          have hz := congrArg Prod.snd (hw z)
          change χ (torusWindingMap m n z)=1 at hz
          rw [hz,mul_one]
        · intro hx
          change χ x=χ a at hx
          let y := a⁻¹*x
          have hchi : χ y=1 := by
            have hh := hmul a y
            have hay : a*y=x := by dsimp [y]; group
            rw [hay,hx] at hh
            exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
          let z := (e y).1
          have hey : e y=(z,1) := Prod.ext rfl hchi
          have hy : y=torusWindingMap m n z := e.injective (hey.trans (hw z).symm)
          refine ⟨z,?_⟩
          change a*torusWindingMap m n z=x
          rw [←hy]
          dsimp [y]
          group
      have hCoordinateCross (c d : Curve Torus) (a b : Circle)
          (hc : c.image={x | x.1=a}) (hd : d.image={x | x.2=b}) :
          CrossesAt c d (a,b) := by
        have hCircle (p : Circle) : ∃ (W : Set Circle) (V : Set ℝ)
            (hp : p∈W) (e : W ≃ₜ V), IsOpen W ∧ IsOpen V ∧ (e ⟨p,hp⟩).val=0 := by
          obtain ⟨r,hr⟩ := Circle.exp_surjective p
          obtain ⟨E,hE,hfun⟩ := Circle.isCoveringMap_exp.isLocalHomeomorph r
          have hp : p∈E.target := by rw [←hr,hfun]; exact E.map_source hE
          let L := Homeomorph.addRight (-r)
          let V := L '' E.source
          let e : E.target ≃ₜ V := E.toHomeomorphSourceTarget.symm.trans (L.image E.source)
          refine ⟨E.target,V,hp,e,E.open_target,L.isOpenMap _ E.open_source,?_⟩
          change E.symm p + (-r)=0
          have he : E.symm p=r := by rw [←hr,hfun];exact E.left_inv hE
          rw [he];ring
        obtain ⟨W₁,V₁,ha,e₁,hW₁,hV₁,he₁⟩ := hCircle a
        obtain ⟨W₂,V₂,hb,e₂,hW₂,hV₂,he₂⟩ := hCircle b
        let W := W₁ ×ˢ W₂
        let V := V₁ ×ˢ V₂
        have hp : (a,b)∈W := ⟨ha,hb⟩
        let e : W ≃ₜ V := (Homeomorph.Set.prod W₁ W₂).trans
          ((e₁.prodCongr e₂).trans (Homeomorph.Set.prod V₁ V₂).symm)
        refine ⟨W,V,hp,e,hW₁.prod hW₂,hV₁.prod hV₂,?_,?_⟩
        · apply Prod.ext
          · exact he₁
          · exact he₂
        · intro x hx
          constructor
          · rw [hc]
            change x.1=a ↔ (e₁ ⟨x.1,hx.1⟩).val=0
            constructor
            · intro h;subst h;exact he₁
            · intro h
              exact congrArg Subtype.val (e₁.injective (Subtype.ext (h.trans he₁.symm)))
          · rw [hd]
            change x.2=b ↔ (e₂ ⟨x.2,hx.2⟩).val=0
            constructor
            · intro h;subst h;exact he₂
            · intro h
              exact congrArg Subtype.val (e₂.injective (Subtype.ext (h.trans he₂.symm)))
      have hContacts (a b : Torus) (m n p q : ℤ) (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
          (range (fun z => a*torusWindingMap m n z) ∩
            range (fun z => b*torusWindingMap p q z)).Subsingleton := by
        let χ : Torus → Circle := fun x => x.1^(-n)*x.2^m
        have hmul (x y : Torus) : χ (x*y)=χ x*χ y := by
          dsimp [χ]
          simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
          ac_rfl
        have hwind (u v : ℤ) (z : Circle) : χ (torusWindingMap u v z)=z^(u*(-n)+v*m) := by
          dsimp [χ,torusWindingMap]
          rw [←zpow_mul,←zpow_mul,←zpow_add]
        have hzero (z : Circle) : χ (a*torusWindingMap m n z)=χ a := by
          rw [hmul,hwind,show m*(-n)+n*m=0 by ring,zpow_zero,mul_one]
        intro x hx y hy
        obtain ⟨z,hz⟩ := hx.1
        obtain ⟨w,hw⟩ := hx.2
        obtain ⟨z',hz'⟩ := hy.1
        obtain ⟨w',hw'⟩ := hy.2
        have he : χ x=χ y := by rw [←hz,←hz',hzero,hzero]
        rw [←hw,←hw',hmul,hmul,hwind,hwind] at he
        have hp := mul_left_cancel he
        have hexp : p*(-n)+q*m=m*q-n*p := by ring
        rw [hexp] at hp
        have hww : w=w' := by
          rcases hdet with hdet|hdet
          · simpa only [hdet,zpow_one] using hp
          · have hi : w⁻¹=w'⁻¹ := by simpa only [hdet,zpow_neg_one] using hp
            exact inv_injective hi
        rw [←hw,←hw',hww]
      have hci : c.image=range (fun z => a*torusWindingMap m n z) := by
        apply congrArg range
        funext z
        exact hc z
      have hdi : d.image=range (fun z => b*torusWindingMap p q z) := by
        apply congrArg range
        funext z
        exact hd z
      have hbez : m*q+n*(-p)=1 := by linear_combination hdet
      let E := actual_integer_basis_torus_homeomorph m n q (-p) hbez
      let e : Torus ≃ₜ Torus := E.trans (Homeomorph.prodComm Circle Circle)
      let C : Curve Torus := ⟨e ∘ c.map,e.isEmbedding.comp c.embedded⟩
      let D : Curve Torus := ⟨e ∘ d.map,e.isEmbedding.comp d.embedded⟩
      have hC (x : Torus) : x∈C.image ↔ e.symm x∈c.image := by
        change x∈range (e ∘ c.map) ↔ e.symm x∈range c.map
        rw [range_comp]
        constructor
        · rintro ⟨y,hy,rfl⟩
          simpa only [e.symm_apply_apply] using hy
        · intro hx
          exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
      have hD (x : Torus) : x∈D.image ↔ e.symm x∈d.image := by
        change x∈range (e ∘ d.map) ↔ e.symm x∈range d.map
        rw [range_comp]
        constructor
        · rintro ⟨y,hy,rfl⟩
          simpa only [e.symm_apply_apply] using hy
        · intro hx
          exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
      have he1 (x : Torus) : (e x).1=x.1^(-n)*x.2^m := rfl
      have he2 (x : Torus) : (e x).2=x.1^q*x.2^(-p) := rfl
      have hchar (x : Torus) : x.1^q*x.2^(-p)=(x.1^(-q)*x.2^p)⁻¹ := by
        simp only [mul_inv_rev,←zpow_neg,neg_neg]
        ac_rfl
      have hCaxis : C.image={x | x.1=(e a).1} := by
        ext x
        rw [hC,hci,hFiber a m n hg]
        change (e.symm x).1^(-n)*(e.symm x).2^m=(e a).1 ↔ x.1=(e a).1
        rw [←he1,e.apply_symm_apply]
      have hDaxis : D.image={x | x.2=(e b).2} := by
        ext x
        rw [hD,hdi,hFiber b p q hg']
        change (e.symm x).1^(-q)*(e.symm x).2^p=b.1^(-q)*b.2^p ↔ x.2=(e b).2
        have hxx : x.2=(e.symm x).1^q*(e.symm x).2^(-p) :=
          (congrArg Prod.snd (e.apply_symm_apply x)).symm
        rw [hxx,he2 b,hchar,hchar]
        exact inv_inj.symm
      refine ⟨?_,?_⟩
      · rw [hci,hdi]
        exact (hContacts a b m n p q (Or.inl hdet)).finite
      · intro y hy
        have heya : (e y).1=(e a).1 := by
          have hh : e y ∈ C.image := (hC (e y)).mpr (by simpa using hy.1)
          simpa only [hCaxis,mem_setOf_eq] using hh
        have heyb : (e y).2=(e b).2 := by
          have hh : e y ∈ D.image := (hD (e y)).mpr (by simpa using hy.2)
          simpa only [hDaxis,mem_setOf_eq] using hh
        have hycoord : e y=((e a).1,(e b).2) := Prod.ext heya heyb
        have hcross : CrossesAt C D (e y) := hycoord.symm ▸
          hCoordinateCross C D (e a).1 (e b).2 hCaxis hDaxis
        obtain ⟨W,V,hyW,h,hW,hV,hzero,haxes⟩ :=
          actual_crossing_axis_chart_lifts_through_local_homeomorph e e.isLocalHomeomorph C D y hcross
        refine ⟨W,V,hyW,h,hW,hV,hzero,?_⟩
        intro x hx
        exact ⟨((hC (e x)).trans (by simp)).symm.trans (haxes x hx).1,
          ((hD (e x)).trans (by simp)).symm.trans (haxes x hx).2⟩
    have hPull {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
        (f : X → Y) (hf : IsOpenEmbedding f) (a b : Curve X) (c d : Curve Y)
        (hc : ∀ z, c.map z=f (a.map z)) (hd : ∀ z, d.map z=f (b.map z))
        (ht : Transverse c d) : Transverse a b := by
      have hci : c.image=f '' a.image := by
        change range c.map=f '' range a.map
        rw [←range_comp]
        exact congrArg range (funext hc)
      have hdi : d.image=f '' b.image := by
        change range d.map=f '' range b.map
        rw [←range_comp]
        exact congrArg range (funext hd)
      have hmemc (x : X) : f x∈c.image ↔ x∈a.image := by
        rw [hci]
        constructor
        · rintro ⟨y,hy,he⟩;exact hf.injective he ▸ hy
        · intro hx;exact ⟨x,hx,rfl⟩
      have hmemd (x : X) : f x∈d.image ↔ x∈b.image := by
        rw [hdi]
        constructor
        · rintro ⟨y,hy,he⟩;exact hf.injective he ▸ hy
        · intro hx;exact ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · apply ht.1.of_injOn (f:=f)
        · intro x hx
          exact ⟨(hmemc x).mpr hx.1,(hmemd x).mpr hx.2⟩
        · exact hf.injective.injOn
      · intro x hx
        obtain ⟨W,V,hxW,h,hW,hV,hzero,haxes⟩ :=
          actual_crossing_axis_chart_lifts_through_local_homeomorph f hf.isLocalHomeomorph c d x
            (ht.2 (f x) ⟨(hmemc x).mpr hx.1,(hmemd x).mpr hx.2⟩)
        exact ⟨W,V,hxW,h,hW,hV,hzero,fun y hy =>
          ⟨(hmemc y).symm.trans (haxes y hy).1,(hmemd y).symm.trans (haxes y hy).2⟩⟩
    have hPush {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
        (f : X → Y) (hf : IsOpenEmbedding f) (a b : Curve X) (c d : Curve Y)
        (hc : ∀ z, c.map z=f (a.map z)) (hd : ∀ z, d.map z=f (b.map z))
        (ht : Transverse a b) : Transverse c d := by
      have hci : c.image=f '' a.image := by
        change range c.map=f '' range a.map
        rw [←range_comp]
        exact congrArg range (funext hc)
      have hdi : d.image=f '' b.image := by
        change range d.map=f '' range b.map
        rw [←range_comp]
        exact congrArg range (funext hd)
      have hmemc (x : X) : f x∈c.image ↔ x∈a.image := by
        rw [hci]
        constructor
        · rintro ⟨y,hy,he⟩
          exact hf.injective he ▸ hy
        · intro hx;exact ⟨x,hx,rfl⟩
      have hmemd (x : X) : f x∈d.image ↔ x∈b.image := by
        rw [hdi]
        constructor
        · rintro ⟨y,hy,he⟩
          exact hf.injective he ▸ hy
        · intro hx;exact ⟨x,hx,rfl⟩
      refine ⟨?_,?_⟩
      · apply (ht.1.image f).subset
        intro y hy
        obtain ⟨x,hx,rfl⟩ := hci ▸ hy.1
        exact ⟨x,⟨hx,(hmemd x).mp hy.2⟩,rfl⟩
      · intro y hy
        obtain ⟨x,hx,rfl⟩ := hci ▸ hy.1
        obtain ⟨W,V,hxW,h,hW,hV,hzero,haxes⟩ := ht.2 x ⟨hx,(hmemd x).mp hy.2⟩
        let E : W ≃ₜ f '' W := hf.isEmbedding.homeomorphImage W
        let e : (f '' W) ≃ₜ V := E.symm.trans h
        have hyW : f x∈f '' W := ⟨x,hxW,rfl⟩
        refine ⟨f '' W,V,hyW,e,hf.isOpenMap W hW,hV,?_,?_⟩
        · have hp : E.symm ⟨f x,hyW⟩=⟨x,hxW⟩ := by
            apply E.injective
            apply Subtype.ext
            exact congrArg Subtype.val (E.apply_symm_apply ⟨f x,hyW⟩)
          change ((h (E.symm ⟨f x,hyW⟩) : V) : ℝ×ℝ)=(0,0)
          rw [hp]
          exact hzero
        · intro z hz
          let w := E.symm ⟨z,hz⟩
          have he : f w.val=z := congrArg Subtype.val (E.apply_symm_apply ⟨z,hz⟩)
          change (z∈c.image ↔ (h w).val.1=0) ∧ (z∈d.image ↔ (h w).val.2=0)
          rw [←he]
          exact ⟨(hmemc w.val).trans (haxes w.val w.property).1,
            (hmemd w.val).trans (haxes w.val w.property).2⟩
    have hContacts (S : Type) [TopologicalSpace S] (U : Set S) (p₀ : Torus)
        (e : U ≃ₜ Punctured p₀) (c d : Curve S)
        (a b : Torus) (m n p q : ℤ)
        (hc : ∀ z, c.map z ∈ U) (hd : ∀ z, d.map z ∈ U)
        (hpc : ∀ z, (e ⟨c.map z,hc z⟩).val=a*torusWindingMap m n z)
        (hpd : ∀ z, (e ⟨d.map z,hd z⟩).val=b*torusWindingMap p q z)
        (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
        (c.image ∩ d.image).Subsingleton := by
      have hContacts (a b : Torus) (m n p q : ℤ) (hdet : m*q-n*p=1 ∨ m*q-n*p = -1) :
          (range (fun z => a*torusWindingMap m n z) ∩
            range (fun z => b*torusWindingMap p q z)).Subsingleton := by
        let χ : Torus → Circle := fun x => x.1^(-n)*x.2^m
        have hmul (x y : Torus) : χ (x*y)=χ x*χ y := by
          dsimp [χ]
          simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
          ac_rfl
        have hwind (u v : ℤ) (z : Circle) : χ (torusWindingMap u v z)=z^(u*(-n)+v*m) := by
          dsimp [χ,torusWindingMap]
          rw [←zpow_mul,←zpow_mul,←zpow_add]
        have hzero (z : Circle) : χ (a*torusWindingMap m n z)=χ a := by
          rw [hmul,hwind,show m*(-n)+n*m=0 by ring,zpow_zero,mul_one]
        intro x hx y hy
        obtain ⟨z,hz⟩ := hx.1
        obtain ⟨w,hw⟩ := hx.2
        obtain ⟨z',hz'⟩ := hy.1
        obtain ⟨w',hw'⟩ := hy.2
        have he : χ x=χ y := by rw [←hz,←hz',hzero,hzero]
        rw [←hw,←hw',hmul,hmul,hwind,hwind] at he
        have hp := mul_left_cancel he
        have hexp : p*(-n)+q*m=m*q-n*p := by ring
        rw [hexp] at hp
        have hww : w=w' := by
          rcases hdet with hdet|hdet
          · simpa only [hdet,zpow_one] using hp
          · have hi : w⁻¹=w'⁻¹ := by simpa only [hdet,zpow_neg_one] using hp
            exact inv_injective hi
        rw [←hw,←hw',hww]
      intro x hx y hy
      obtain ⟨z,hz⟩ := hx.1
      obtain ⟨w,hw⟩ := hx.2
      obtain ⟨z',hz'⟩ := hy.1
      obtain ⟨w',hw'⟩ := hy.2
      have hxU : x ∈ U := hz ▸ hc z
      have hyU : y ∈ U := hz' ▸ hc z'
      have hval : (e ⟨x,hxU⟩).val=(e ⟨y,hyU⟩).val := by
        apply hContacts a b m n p q hdet
        · constructor
          · exact ⟨z,by simpa only [hz] using (hpc z).symm⟩
          · exact ⟨w,by simpa only [hw] using (hpd w).symm⟩
        · constructor
          · exact ⟨z',by simpa only [hz'] using (hpc z').symm⟩
          · exact ⟨w',by simpa only [hw'] using (hpd w').symm⟩
      exact congrArg Subtype.val (e.injective (Subtype.ext hval))
    have ht : Transverse (fill a) (fill b) := by
      rcases hdet with hdet|hdet
      · exact hTorus (fill a) (fill b) A B m n p q hg hg' hdet ha hb
      · apply transverse_symm_of_chart
        exact hTorus (fill b) (fill a) B A p q m n hg' hg
          (by linear_combination -hdet) hb ha
    have hval : IsOpenEmbedding (Subtype.val : Punctured p₀ → Torus) :=
      (isOpen_ne : IsOpen {x : Torus | x ≠ p₀}).isOpenEmbedding_subtypeVal
    have hab : Transverse a b := hPull Subtype.val hval a b (fill a) (fill b)
      (fun _ => rfl) (fun _ => rfl) ht
    let f : Punctured p₀ → S := fun x => (e.symm x).val
    have hf : IsOpenEmbedding f := hU.isOpenEmbedding_subtypeVal.comp e.symm.isOpenEmbedding
    have hcd : Transverse c.val d.val := hPush f hf a b c.val d.val (fun z => (hc z).symm) (fun z => (hd z).symm) hab
    have hcU (z : Circle) : c.val.map z∈U := hc z ▸ (e.symm (a.map z)).property
    have hdU (z : Circle) : d.val.map z∈U := hd z ▸ (e.symm (b.map z)).property
    have hpc (z : Circle) : (e ⟨c.val.map z,hcU z⟩).val=A*torusWindingMap m n z := by
      have hz : (⟨c.val.map z,hcU z⟩ : U)=e.symm (a.map z) := Subtype.ext (hc z).symm
      rw [hz,e.apply_symm_apply]
      exact ha z
    have hpd (z : Circle) : (e ⟨d.val.map z,hdU z⟩).val=B*torusWindingMap p q z := by
      have hz : (⟨d.val.map z,hdU z⟩ : U)=e.symm (b.map z) := Subtype.ext (hd z).symm
      rw [hz,e.apply_symm_apply]
      exact hb z
    have hsub := hContacts S U p₀ e c.val d.val A B m n p q hcU hdU hpc hpd hdet
    have hcard : hcd.1.toFinset.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro x hx y hy
      exact hsub (hcd.1.mem_toFinset.mp hx) (hcd.1.mem_toFinset.mp hy)
    exact (Nat.sInf_le (show hcd.1.toFinset.card ∈ intersectionCounts
      (Quotient.mk (essentialCurveSetoid S) c) (Quotient.mk (essentialCurveSetoid S) d) from
        ⟨c,d,rfl,rfl,hcd,rfl⟩)).trans hcard
  have hFareyDet (s t : FareySlope) (h : FareyAdjacent s t) :
      (slopeDirection s).1*(slopeDirection t).2-(slopeDirection s).2*(slopeDirection t).1=1 ∨
      (slopeDirection s).1*(slopeDirection t).2-(slopeDirection s).2*(slopeDirection t).1 = -1 := by
    cases s with
    | none =>
      cases t with
      | none => exact h.elim
      | some q =>
        change q.den=1 at h
        left
        simp [slopeDirection,h]
    | some p =>
      cases t with
      | none =>
        change p.den=1 at h
        right
        simp [slopeDirection,h]
      | some q =>
        change Int.natAbs (p.num*(q.den:ℤ)-q.num*(p.den:ℤ))=1 at h
        have hh : Int.natAbs (p.num*(q.den:ℤ)-q.num*(p.den:ℤ))=Int.natAbs (1:ℤ) := h
        simpa only [slopeDirection,mul_comm] using Int.natAbs_eq_natAbs_iff.mp hh
  have hUpperU (s t : FareySlope) (h : FareyAdjacent s t) :
      geometricIntersection (vertex (.inl s))
        (vertex (.inl t)) ≤ 1 := by
    exact hSideUpper S U hU (1,1) eU (F s) (F t)
      ⟨GU s,hEssU s⟩ ⟨GU t,hEssU t⟩ (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (hPrimitive s) (hPrimitive t) (hParam s) (hParam t) (fun _ => rfl) (fun _ => rfl)
      (hFareyDet s t h)
  have hUpperV (s t : FareySlope) (h : FareyAdjacent s t) :
      geometricIntersection (vertex (.inr s))
        (vertex (.inr t)) ≤ 1 := by
    exact hSideUpper S V hV (1,1) eV (F s) (F t)
      ⟨GV s,hEssV s⟩ ⟨GV t,hEssV t⟩ (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (hPrimitive s) (hPrimitive t) (hParam s) (hParam t) (fun _ => rfl) (fun _ => rfl)
      (hFareyDet s t h)
  have hcross : ∀ s t, Disjoint (GU s).image (GV t).image := by
    intro s t
    exact hUV.mono (hGU s) (hGV t)
  have hboundaryU : ∀ s, Disjoint c.val.image (GU s).image := by
    intro s
    apply Set.disjoint_left.mpr
    intro x hxc hxG
    have hx : x ∈ U ∪ V := Or.inl (hGU s hxG)
    rw [hcover] at hx
    exact hx hxc
  have hboundaryV : ∀ s, Disjoint c.val.image (GV s).image := by
    intro s
    apply Set.disjoint_left.mpr
    intro x hxc hxG
    have hx : x ∈ U ∪ V := Or.inr (hGV s hxG)
    rw [hcover] at hx
    exact hx hxc
  have hcrossIntersection (s t : FareySlope) :
      geometricIntersection (vertex (.inl s)) (vertex (.inr t))=0 :=
    geometricIntersection_eq_zero_of_disjoint_representatives
      ⟨GU s,hEssU s⟩ ⟨GV t,hEssV t⟩ (hcross s t)
  have hboundaryIntersection : ∀ slope : Sum FareySlope FareySlope, geometricIntersection v.val (vertex slope)=0 := by
    intro slope
    rw [←hcv]
    cases slope with
    | inl s =>
      exact geometricIntersection_eq_zero_of_disjoint_representatives c
        ⟨GU s,hEssU s⟩ (hboundaryU s)
    | inr s =>
      exact geometricIntersection_eq_zero_of_disjoint_representatives c
        ⟨GV s,hEssV s⟩ (hboundaryV s)
  obtain ⟨qU,hqU,hqUOut⟩ := hCollapse U hU (1,1) eU
  obtain ⟨qV,hqV,hqVOut⟩ := hCollapse V hV (1,1) eV
  have hqUGU : ∀ s z, qU ((GU s).map z)=A s*torusWindingMap
      (slopeDirection s).1 (slopeDirection s).2 z := by
    intro s z
    rw [show (GU s).map z=(eU.symm ((F s).map z)).val from rfl,hqU,eU.apply_symm_apply]
    exact hParam s z
  have hqVGV : ∀ s z, qV ((GV s).map z)=A s*torusWindingMap
      (slopeDirection s).1 (slopeDirection s).2 z := by
    intro s z
    rw [show (GV s).map z=(eV.symm ((F s).map z)).val from rfl,hqV,eV.apply_symm_apply]
    exact hParam s z
  have hLeftInject : ∀ s t, vertex (.inl s)=vertex (.inl t) → s=t := by
    intro s t he
    exact hSlopeInject qU GU A hqUGU s t (Quotient.exact he)
  have hRightInject : ∀ s t, vertex (.inr s)=vertex (.inr t) → s=t := by
    intro s t he
    exact hSlopeInject qV GV A hqVGV s t (Quotient.exact he)
  have hCrossNe : ∀ s t, vertex (.inl s) ≠ vertex (.inr t) := by
    intro s t he
    let m := (slopeDirection s).1
    let n := (slopeDirection s).2
    let u := Int.gcdA m n
    let w := Int.gcdB m n
    have hbez : m*u+n*w=1 := by
      have hh := Int.gcd_eq_gcd_ab m n
      rw [hPrimitive s] at hh
      exact hh.symm
    let χ : C(Torus,Circle) := ⟨fun y => ((A s).1⁻¹*y.1)^u*((A s).2⁻¹*y.2)^w,by fun_prop⟩
    have hcoord : ∀ z, (χ.comp qU) ((GU s).map z)=z := by
      intro z
      change ((A s).1⁻¹*(qU ((GU s).map z)).1)^u*
        ((A s).2⁻¹*(qU ((GU s).map z)).2)^w=z
      rw [hqUGU]
      simp only [Prod.fst_mul,Prod.snd_mul,torusWindingMap,←mul_assoc,
        inv_mul_cancel,mul_one,one_mul]
      rw [←zpow_mul,←zpow_mul,←zpow_add,hbez,zpow_one]
    apply hExclude (GU s) (GV t) (χ.comp qU) hcoord (χ (1,1)) _ (Quotient.exact he)
    intro z
    change χ (qU ((GV t).map z))=χ (1,1)
    rw [hqUOut]
    intro hx
    exact Set.disjoint_left.mp hUV hx (hGV t (Set.mem_range_self z))
  have hVertexInjective : Function.Injective vertex := by
    intro a b he
    cases a with
    | inl s =>
      cases b with
      | inl t => exact congrArg Sum.inl (hLeftInject s t he)
      | inr t => exact (hCrossNe s t he).elim
    | inr s =>
      cases b with
      | inl t => exact (hCrossNe t s he.symm).elim
      | inr t => exact congrArg Sum.inr (hRightInject s t he)
  have hVertexNS : ∀ slope, nonseparatingVertex (vertex slope) := by
    intro slope
    cases slope with
    | inl s => exact (hDerivedU s).2
    | inr s => exact (hDerivedV s).2
  have hVertexNe : ∀ slope, v.val ≠ vertex slope := by
    intro slope he
    have hv := (separatingVertex_iff_not_nonseparatingVertex S v.val).mp v.property
    exact hv (he.symm ▸ hVertexNS slope)
  have hVertexLink : ∀ slope, LinkFace geometricIntersection v.val {vertex slope} := by
    intro slope
    constructor
    · simpa using hVertexNe slope
    · intro a ha b hb hab
      simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at ha hb
      rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
      · exact (hab rfl).elim
      · rw [hboundaryIntersection]; omega
      · rw [geometricIntersection_symm_of_chart,hboundaryIntersection]; omega
      · exact (hab rfl).elim
  have hlinkZero : ∀ w : Vertex S, LinkFace geometricIntersection v.val {w} →
      geometricIntersection v.val w = 0 := by
    intro w hw
    apply hsmall v.val w v.property
    exact hw.2 (by simp) (by simp) (by
      intro hh
      apply hw.1
      simp [hh])
  have hactualSide : ∀ w : Vertex S, LinkFace geometricIntersection v.val {w} →
      ∃ d : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) d = w ∧
        Disjoint c.val.image d.val.image ∧ (d.val.image ⊆ U ∨ d.val.image ⊆ V) := by
    intro w hw
    obtain ⟨d,hd,hdis⟩ := hfixed c w (by rw [hcv]; exact hlinkZero w hw)
    have hsub : d.val.image ⊆ c.val.imageᶜ := by
      intro x hx hxc
      exact Set.disjoint_left.mp hdis hxc hx
    have hconn : IsConnected d.val.image := isConnected_range d.val.embedded.continuous
    have hsides : d.val.image ⊆ U ∨ d.val.image ⊆ V :=
      hconn.isPreconnected.subset_or_subset hU hV hUV (hcover.symm ▸ hsub)
    exact ⟨d,hd,hdis,hsides⟩
  have hPuncturedRepresentative (W : Set S) (p : Torus)
      (e : W ≃ₜ Punctured p) (a : Curve S) (ha : a.image ⊆ W) :
      ∃ b : Curve (Punctured p), ∀ z, (e.symm (b.map z)).val=a.map z := by
    let b : Curve (Punctured p) := {
      map := fun z => e ⟨a.map z,ha (mem_range_self z)⟩
      embedded := e.isEmbedding.comp
        ((_root_.Topology.IsEmbedding.of_comp_iff
          (g := Subtype.val) _root_.Topology.IsEmbedding.subtypeVal).mp a.embedded)
    }
    exact ⟨b,fun z => congrArg Subtype.val (e.symm_apply_apply _)⟩
  have hFilledDiskInterior (S : Type) [TopologicalSpace S] (U : Set S)
      (p : Torus) (e : U ≃ₜ Punctured p)
      (c : Curve S) (hc : Essential c) (d : Curve (Punctured p))
      (hparam : ∀ z, (e.symm (d.map z)).val=c.map z)
      (f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus))
      (hf : IsEmbedding f)
      (hboundary : f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = (fill d).image) :
      ∃ x, f x=p ∧ (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 := by
    have hcontain : p ∈ range f := by
      classical
      by_contra havoid
      have hav (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : f x ≠ p := by
        intro hx
        exact havoid ⟨x,hx⟩
      let fp : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Punctured p) :=
        ⟨fun x => ⟨f x,hav x⟩,f.continuous.subtype_mk _⟩
      have hfp : IsEmbedding fp := by
        apply (IsEmbedding.of_comp_iff (g := Subtype.val) IsEmbedding.subtypeVal).mp
        exact hf
      let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
        ⟨fun x => (e.symm (fp x)).val,
          continuous_subtype_val.comp (e.symm.continuous.comp fp.continuous)⟩
      apply hc
      refine ⟨g,IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hfp),?_⟩
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        have hb : f y ∈ (fill d).image := hboundary ▸ ⟨y,hy,rfl⟩
        obtain ⟨z,hz⟩ := hb
        have he : d.map z=fp y := Subtype.ext hz
        refine ⟨z,?_⟩
        rw [←hparam z,he]
        rfl
      · rintro ⟨z,rfl⟩
        have hz : (d.map z).val ∈ (fill d).image := mem_range_self z
        rw [←hboundary] at hz
        obtain ⟨y,hy,hyz⟩ := hz
        refine ⟨y,hy,?_⟩
        change (e.symm (fp y)).val=c.map z
        have he : fp y=d.map z := Subtype.ext hyz
        rw [he,hparam z]
    obtain ⟨x,hx⟩ := hcontain
    have hnot : (x : EuclideanSpace ℝ (Fin 2)) ∉ Metric.sphere 0 1 := by
      intro hs
      have hb : p ∈ (fill d).image := hboundary ▸ ⟨x,hs,hx⟩
      obtain ⟨z,hz⟩ := hb
      exact (d.map z).property hz
    refine ⟨x,hx,?_⟩
    rw [Metric.mem_ball]
    have hle := x.property
    rw [Metric.mem_closedBall] at hle
    have hne : dist (x : EuclideanSpace ℝ (Fin 2)) 0 ≠ 1 := by
      simpa only [Metric.mem_sphere] using hnot
    exact lt_of_le_of_ne hle hne
  have hJoinUpper (s t : Sum FareySlope FareySlope) (h : FareyJoinAdjacent s t) :
      geometricIntersection (vertex s) (vertex t) ≤ 1 := by
    cases s with
    | inl s =>
      cases t with
      | inl t => exact hUpperU s t h
      | inr t => rw [hcrossIntersection]; omega
    | inr s =>
      cases t with
      | inl t => rw [geometricIntersection_symm_of_chart,hcrossIntersection]; omega
      | inr t => exact hUpperV s t h
  have hFareyFaceLink (σ : Finset (Sum FareySlope FareySlope))
      (h : FareyJoinFace σ) : LinkFace geometricIntersection v.val (σ.image vertex) := by
    constructor
    · intro hv
      obtain ⟨s,hs,he⟩ := Finset.mem_image.mp hv
      exact hVertexNe s he.symm
    · intro a ha b hb hab
      simp only [Finset.mem_coe,Finset.mem_insert] at ha hb
      rcases ha with rfl|ha
      · rcases hb with rfl|hb
        · exact (hab rfl).elim
        · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hb
          rw [hboundaryIntersection];omega
      · rcases hb with rfl|hb
        · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ha
          rw [geometricIntersection_symm_of_chart,hboundaryIntersection];omega
        · obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp ha
          obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hb
          exact hJoinUpper s t (h hs ht (fun he => hab (congrArg vertex he)))
  have hSupportedClassTransport (S : Type) [TopologicalSpace S] [T2Space S] [CompactSpace S]
      (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p)
      (a b : Curve (Punctured p)) (c d : Curve S)
      (hc : ∀ z, (e.symm (a.map z)).val = c.map z)
      (hd : ∀ z, (e.symm (b.map z)).val = d.map z)
      (H : AmbientIsotopy (Punctured p)) (K : Set (Punctured p))
      (hK : IsCompact K) (hFix : ∀ t x, x ∉ K → H.map (t,x)=x)
      (hH : H.finalMap '' a.image = b.image) :
      AmbientIsotopy.Rel c.image d.image := by
    have hExtendP : ∃ G : AmbientIsotopy S,
        (∀ (t : CurveComplex.Interval) (x : U), G.map (t,x.val)=(e.symm (H.map (t,e x))).val) ∧
        (∀ t x, x ∉ U → G.map (t,x)=x) := by
      classical
      have hExtend (U K : Set S) (hU : IsOpen U) (hK : IsClosed K) (hKU : K ⊆ U)
          (H : AmbientIsotopy U)
          (hfix : ∀ t (x : U), x.val ∉ K → (H.map (t, x) : S) = x.val) :
          ∃ G : AmbientIsotopy S,
            (∀ t (x : U), G.map (t, x.val) = (H.map (t, x) : S)) ∧
            (∀ t x, x ∉ K → G.map (t, x) = x) := by
        classical
        let F : CurveComplex.Interval × S → S := fun z =>
          if hx : z.2 ∈ U then (H.map (z.1, ⟨z.2, hx⟩) : S) else z.2
        have hFU (t : CurveComplex.Interval) (x : U) : F (t, x.val) = (H.map (t, x) : S) := by
          simp only [F, dif_pos x.property]
        have hFK (t : CurveComplex.Interval) (x : S) (hx : x ∉ K) : F (t, x) = x := by
          dsimp [F]
          split_ifs with h
          · exact hfix t ⟨x, h⟩ hx
          · rfl
        have hcontU : ContinuousOn F {z | z.2 ∈ U} := by
          apply continuousOn_iff_continuous_domRestrict.mpr
          have hh : Continuous (fun z : {z : CurveComplex.Interval × S | z.2 ∈ U} =>
              (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) :=
            continuous_subtype_val.comp (H.map.continuous.comp
              ((continuous_fst.comp continuous_subtype_val).prodMk
                ((continuous_snd.comp continuous_subtype_val).subtype_mk _)))
          have hsame : ({z : CurveComplex.Interval × S | z.2 ∈ U}.domRestrict F) =
              (fun z : {z : CurveComplex.Interval × S | z.2 ∈ U} =>
                (H.map (z.val.1, ⟨z.val.2, z.property⟩) : S)) := by
            funext z
            exact hFU z.val.1 ⟨z.val.2, z.property⟩
          rw [hsame]
          exact hh
        have hcontK : ContinuousOn F {z | z.2 ∉ K} := by
          apply continuous_snd.continuousOn.congr
          intro z hz
          exact hFK z.1 z.2 hz
        have hcont : Continuous F := by
          rw [continuous_iff_continuousAt]
          intro z
          by_cases hz : z.2 ∈ U
          · exact hcontU.continuousAt ((hU.preimage continuous_snd).mem_nhds hz)
          · exact hcontK.continuousAt
              ((hK.isOpen_compl.preimage continuous_snd).mem_nhds (fun hk => hz (hKU hk)))
        have hmem (t : CurveComplex.Interval) (x : S) : F (t, x) ∈ U ↔ x ∈ U := by
          by_cases hx : x ∈ U
          · rw [hFU t ⟨x, hx⟩]
            exact iff_of_true (H.map (t, ⟨x, hx⟩)).property hx
          · simp only [F, dif_neg hx, hx]
        refine ⟨{ map := ⟨F, hcont⟩, homeomorphism_at := ?_, at_zero := ?_ }, hFU, hFK⟩
        · intro t
          obtain ⟨e, he⟩ := H.homeomorphism_at t
          have hinj : Function.Injective (fun x => F (t, x)) := by
            intro x y hxy
            change F (t, x) = F (t, y) at hxy
            by_cases hx : x ∈ U
            · have hy : y ∈ U := (hmem t y).mp (hxy ▸ (hmem t x).mpr hx)
              have heq : e ⟨x, hx⟩ = e ⟨y, hy⟩ := by
                apply Subtype.ext
                simpa only [he, hFU t ⟨x, hx⟩, hFU t ⟨y, hy⟩] using hxy
              exact congrArg Subtype.val (e.injective heq)
            · have hy : y ∉ U := by
                intro hy
                exact hx ((hmem t x).mp (hxy.symm ▸ (hmem t y).mpr hy))
              simpa only [F, dif_neg hx, dif_neg hy] using hxy
          have hsurj : Function.Surjective (fun x => F (t, x)) := by
            intro y
            by_cases hy : y ∈ U
            · refine ⟨(e.symm ⟨y, hy⟩).val, ?_⟩
              change F (t, (e.symm ⟨y, hy⟩).val) = y
              rw [hFU]
              have hh := congrArg Subtype.val (e.apply_symm_apply ⟨y, hy⟩)
              simpa only [he] using hh
            · exact ⟨y, by simp only [F, dif_neg hy]⟩
          have hh : IsHomeomorph (fun x => F (t, x)) :=
            (isHomeomorph_iff_continuous_bijective).mpr
              ⟨hcont.comp (continuous_const.prodMk continuous_id), hinj, hsurj⟩
          obtain ⟨e, he⟩ := isHomeomorph_iff_exists_homeomorph.mp hh
          exact ⟨e, fun x => congrFun he x⟩
        · intro x
          dsimp [F]
          split_ifs with hx
          · exact congrArg Subtype.val (H.at_zero ⟨x, hx⟩)
          · rfl
      let L : AmbientIsotopy U := {
        map := ⟨fun z => e.symm (H.map (z.1,e z.2)),
          e.symm.continuous.comp (H.map.continuous.comp
            (continuous_fst.prodMk (e.continuous.comp continuous_snd)))⟩
        homeomorphism_at := by
          intro t
          obtain ⟨h,hh⟩ := H.homeomorphism_at t
          exact ⟨(e.trans h).trans e.symm,fun x => congrArg e.symm (hh (e x))⟩
        at_zero := by
          intro x
          change e.symm (H.map (⟨0,by norm_num⟩,e x))=x
          rw [H.at_zero,e.symm_apply_apply]
      }
      let C : Set S := (fun x : Punctured p => (e.symm x).val) '' K
      have hC : IsCompact C := hK.image (continuous_subtype_val.comp e.symm.continuous)
      have hCU : C ⊆ U := by
        rintro x ⟨y,hy,rfl⟩
        exact (e.symm y).property
      have hLfix : ∀ t (x : U), x.val ∉ C → (L.map (t,x)).val=x.val := by
        intro t x hx
        have heK : e x ∉ K := by
          intro hk
          apply hx
          exact ⟨e x,hk,congrArg Subtype.val (e.symm_apply_apply x)⟩
        change (e.symm (H.map (t,e x))).val=x.val
        rw [hFix t (e x) heK,e.symm_apply_apply]
      obtain ⟨G,hGU,hGfix⟩ := hExtend U C hU hC.isClosed hCU L hLfix
      refine ⟨G,hGU,?_⟩
      intro t x hx
      exact hGfix t x (fun hxc => hx (hCU hxc))
    obtain ⟨G,hG,hGoutside⟩ := hExtendP
    refine ⟨G,?_⟩
    ext x
    constructor
    · rintro ⟨y,⟨z,rfl⟩,rfl⟩
      have heq : G.finalMap (c.map z)=(e.symm (H.finalMap (a.map z))).val := by
        rw [←hc z]
        simpa only [AmbientIsotopy.finalMap,e.apply_symm_apply] using
          hG ⟨1,by norm_num⟩ (e.symm (a.map z))
      rw [heq]
      have hm : H.finalMap (a.map z) ∈ b.image := hH ▸ ⟨a.map z,mem_range_self z,rfl⟩
      obtain ⟨w,hw⟩ := hm
      refine ⟨w,?_⟩
      rw [←hd w,hw]
    · rintro ⟨w,rfl⟩
      have hm : b.map w ∈ H.finalMap '' a.image := hH.symm ▸ mem_range_self w
      obtain ⟨y,⟨z,rfl⟩,hz⟩ := hm
      refine ⟨c.map z,mem_range_self z,?_⟩
      rw [←hc z,←hd w]
      change G.map (⟨1,by norm_num⟩,(e.symm (a.map z)).val)=(e.symm (b.map w)).val
      rw [hG,e.apply_symm_apply]
      exact congrArg (fun q : Punctured p => (e.symm q).val) hz
  have hSourceLowerCount (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (U : Set S) (hU : IsOpen U) (p₀ : Torus) (e : U ≃ₜ Punctured p₀)
      (a b : Curve (Punctured p₀)) (c d : EssentialCurve S)
      (A B : Torus) (m n p q : ℤ) (hg : m.gcd n=1)
      (ha : ∀ z, (a.map z).val=A*torusWindingMap m n z)
      (hb : ∀ z, (b.map z).val=B*torusWindingMap p q z)
      (hc : ∀ z, (e.symm (a.map z)).val=c.val.map z)
      (hd : ∀ z, (e.symm (b.map z)).val=d.val.map z)
      (hle : geometricIntersection (Quotient.mk (essentialCurveSetoid S) c)
        (Quotient.mk (essentialCurveSetoid S) d) ≤ 1) :
      Int.natAbs (m*q-n*p)≤1 := by
    have hCollapse (S : Type) [TopologicalSpace S] [T2Space S]
        (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p) :
        ∃ q : C(S,Torus), (∀ x : U, q x.val = (e x).val) ∧
          (∀ x, x ∉ U → q x = p) := by
      classical
      let q : S → Torus := fun x => if hx : x ∈ U then (e ⟨x,hx⟩).val else p
      have hqU (x : U) : q x.val=(e x).val := by simp [q,x.property]
      have hqOut (x : S) (hx : x ∉ U) : q x=p := by simp [q,hx]
      have hq : Continuous q := by
        apply continuous_def.mpr
        intro O hO
        by_cases hp : p ∈ O
        · let K : Set Torus := Oᶜ
          have hK : IsCompact K := hO.isClosed_compl.isCompact
          letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
          have hKp : ∀ x ∈ K, x ≠ p := by
            intro x hx he
            exact hx (he ▸ hp)
          let f : K → S := fun x => (e.symm ⟨x.val,hKp x.val x.property⟩).val
          have hf : Continuous f := continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
          have hr : IsCompact (range f) := isCompact_range hf
          have heq : q ⁻¹' O = (range f)ᶜ := by
            ext x
            constructor
            · intro hx
              rintro ⟨y,hy⟩
              have hxU : x ∈ U := hy ▸ (e.symm ⟨y.val,hKp y.val y.property⟩).property
              have hqv : q x=y.val := by
                rw [←hy,hqU]
                exact congrArg Subtype.val (e.apply_symm_apply _)
              exact y.property (hqv ▸ hx)
            · intro hx
              change q x ∈ O
              by_cases hxU : x ∈ U
              · rw [show q x=(e ⟨x,hxU⟩).val from hqU ⟨x,hxU⟩]
                by_contra hn
                apply hx
                refine ⟨⟨(e ⟨x,hxU⟩).val,hn⟩,?_⟩
                change (e.symm (e ⟨x,hxU⟩)).val=x
                rw [e.symm_apply_apply]
              · rw [hqOut x hxU]
                exact hp
          rw [heq]
          exact hr.isClosed.isOpen_compl
        · have heq : q ⁻¹' O = Subtype.val ''
              ((fun x : U => (e x).val) ⁻¹' O) := by
            ext x
            constructor
            · intro hx
              have hxU : x ∈ U := by
                by_contra hn
                exact hp ((hqOut x hn) ▸ hx)
              refine ⟨⟨x,hxU⟩,?_,rfl⟩
              change (e ⟨x,hxU⟩).val ∈ O
              change q x ∈ O at hx
              rw [hqU ⟨x,hxU⟩] at hx
              exact hx
            · rintro ⟨y,hy,rfl⟩
              change q y.val ∈ O
              change (e y).val ∈ O at hy
              rw [hqU y]
              exact hy
          rw [heq]
          exact hU.isOpenMap_subtype_val _ (hO.preimage
            (continuous_subtype_val.comp e.continuous))
      exact ⟨⟨q,hq⟩,hqU,hqOut⟩
    have hExactFiber (S : Type) [TopologicalSpace S] (U : Set S) (p : Torus)
        (e : U ≃ₜ Punctured p) (q : C(S,Torus))
        (hq : ∀ x : U, q x.val=(e x).val) (hout : ∀ x, x∉U → q x=p)
        (a : Curve (Punctured p)) (c : Curve S)
        (hc : ∀ z, (e.symm (a.map z)).val=c.map z)
        (A : Torus) (m n : ℤ) (hgcd : m.gcd n=1)
        (hparam : ∀ z, (a.map z).val=A*torusWindingMap m n z) :
        {x : S | (q x).1^(-n)*(q x).2^m=A.1^(-n)*A.2^m}=c.image := by
      have hPrimitiveFiber (a : Torus) (m n : ℤ) (hgcd : m.gcd n=1) :
          range (fun z => a*torusWindingMap m n z) =
            {x | x.1^(-n)*x.2^m=a.1^(-n)*a.2^m} := by
        let u := Int.gcdA m n
        let v := Int.gcdB m n
        have hbez : m*u+n*v=1 := by
          have h := Int.gcd_eq_gcd_ab m n
          rw [hgcd] at h
          exact h.symm
        let e := actual_integer_basis_torus_homeomorph m n u v hbez
        let χ : Torus → Circle := fun x => x.1^(-n)*x.2^m
        have hmul (x y : Torus) : χ (x*y)=χ x*χ y := by
          dsimp [χ]
          simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
          ac_rfl
        have hw (z : Circle) : e (torusWindingMap m n z)=(z,1) := by
          apply Prod.ext
          · change (z^m)^u*(z^n)^v=z
            rw [←zpow_mul,←zpow_mul,←zpow_add,hbez,zpow_one]
          · change (z^m)^(-n)*(z^n)^m=1
            rw [←zpow_mul,←zpow_mul,←zpow_add,show m*(-n)+n*m=0 by ring,zpow_zero]
        ext x
        constructor
        · rintro ⟨z,rfl⟩
          change χ (a*torusWindingMap m n z)=χ a
          rw [hmul]
          have hz := congrArg Prod.snd (hw z)
          change χ (torusWindingMap m n z)=1 at hz
          rw [hz,mul_one]
        · intro hx
          change χ x=χ a at hx
          let y := a⁻¹*x
          have hchi : χ y=1 := by
            have hh := hmul a y
            have hay : a*y=x := by dsimp [y]; group
            rw [hay,hx] at hh
            exact mul_left_cancel (hh.symm.trans (mul_one _).symm)
          let z := (e y).1
          have hey : e y=(z,1) := Prod.ext rfl hchi
          have hy : y=torusWindingMap m n z := e.injective (hey.trans (hw z).symm)
          refine ⟨z,?_⟩
          change a*torusWindingMap m n z=x
          rw [←hy]
          dsimp [y]
          group
      have havoid : A.1^(-n)*A.2^m≠p.1^(-n)*p.2^m := by
        intro he
        have hp : p∈range (fun z => A*torusWindingMap m n z) := by
          rw [hPrimitiveFiber A m n hgcd]
          exact he.symm
        obtain ⟨z,hz⟩ := hp
        exact (a.map z).property ((hparam z).trans hz)
      have hU (z : Circle) : c.map z∈U := hc z ▸ (e.symm (a.map z)).property
      have hPin (z : Circle) : q (c.map z)=A*torusWindingMap m n z := by
        rw [←hc z,hq,e.apply_symm_apply]
        exact hparam z
      ext x
      constructor
      · intro hx
        change (q x).1^(-n)*(q x).2^m=A.1^(-n)*A.2^m at hx
        have hxU : x∈U := by
          by_contra h
          rw [hout x h] at hx
          exact havoid hx.symm
        have hchar : (e ⟨x,hxU⟩).val ∈ range (fun z => A*torusWindingMap m n z) := by
          rw [hPrimitiveFiber A m n hgcd]
          simpa only [hq ⟨x,hxU⟩,mem_setOf_eq] using hx
        obtain ⟨z,hz⟩ := hchar
        have he : a.map z=e ⟨x,hxU⟩ := Subtype.ext ((hparam z).trans hz)
        refine ⟨z,?_⟩
        rw [←hc z,he,e.symm_apply_apply]
      · rintro ⟨z,rfl⟩
        change (q (c.map z)).1^(-n)*(q (c.map z)).2^m=A.1^(-n)*A.2^m
        rw [hPin z]
        have hz : A*torusWindingMap m n z ∈ range (fun z => A*torusWindingMap m n z) := mem_range_self z
        rw [hPrimitiveFiber A m n hgcd] at hz
        exact hz
    have hSourceCircle (S : Type) [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
        (c d : EssentialCurve S) (χ : C(S,Circle)) (θ A : Circle) (k : ℤ)
        (hfiber : {x : S | χ x=θ}=c.val.image)
        (hparam : ∀ z, χ (d.val.map z)=A*z^k)
        (hle : geometricIntersection (Quotient.mk (essentialCurveSetoid S) c)
          (Quotient.mk (essentialCurveSetoid S) d) ≤ 1) :
        ∃ f : C(Circle,Circle),
          Nonempty ((⟨fun z : Circle => A*z^k,by fun_prop⟩ : C(Circle,Circle)).Homotopy f) ∧
          {z : Circle | f z=θ}.Subsingleton := by
      have hFixedSmall (S : Type) [TopologicalSpace S]
          [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
          (c : EssentialCurve S) (w : Vertex S)
          (hle : geometricIntersection (Quotient.mk (essentialCurveSetoid S) c) w ≤ 1) :
          ∃ d : EssentialCurve S, Quotient.mk (essentialCurveSetoid S) d=w ∧
            (c.val.image ∩ d.val.image).Subsingleton := by
        classical
        letI : ClosedSurface S := Classical.choice hS.2.1
        obtain ⟨a,d,ha,hd,ht,hcard⟩ := source_geometric_intersection_attained S
          (Quotient.mk (essentialCurveSetoid S) c) w
        have hsub : (a.val.image ∩ d.val.image).Subsingleton := by
          have hsmall : ht.1.toFinset.card≤1 := hcard ▸ hle
          have hsmall' := Finset.card_le_one.mp hsmall
          intro x hx y hy
          exact hsmall' x (ht.1.mem_toFinset.mpr hx) y (ht.1.mem_toFinset.mpr hy)
        have hac : AmbientIsotopy.Rel a.val.image c.val.image := Quotient.exact ha
        obtain ⟨H,hH⟩ := hac
        obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
        let out : Curve S := ⟨e ∘ d.val.map,e.isEmbedding.comp d.val.embedded⟩
        have hOut : out.image=H.finalMap '' d.val.image := by
          change range (e ∘ d.val.map)=H.finalMap '' range d.val.map
          rw [range_comp]
          exact image_congr (fun x _ => he x)
        have hdout : AmbientIsotopy.Rel d.val.image out.image := ⟨H,hOut.symm⟩
        let outc : EssentialCurve S := ⟨out,(essential_isotopy_invariant hdout).mp d.property⟩
        refine ⟨outc,(Quotient.sound hdout).symm.trans hd,?_⟩
        change (c.val.image ∩ out.image).Subsingleton
        have heq : H.finalMap=e := funext (fun x => (he x).symm)
        rw [←hH,hOut,heq,←image_inter e.injective]
        exact hsub.image e
      obtain ⟨b,hb,hcontact⟩ := hFixedSmall S hS c
        (Quotient.mk (essentialCurveSetoid S) d) hle
      have hrel : AmbientIsotopy.Rel d.val.image b.val.image := Quotient.exact hb.symm
      obtain ⟨H,hH⟩ := hrel
      obtain ⟨e,he⟩ := H.homeomorphism_at ⟨1,by norm_num⟩
      let f : C(Circle,Circle) := ⟨fun z => χ (H.finalMap (d.val.map z)),
        χ.continuous.comp (H.map.continuous.comp
          (continuous_const.prodMk d.val.embedded.continuous))⟩
      let G : (⟨fun z : Circle => A*z^k,by fun_prop⟩ : C(Circle,Circle)).Homotopy f := {
        toContinuousMap := ⟨fun tz => χ (H.map (tz.1,d.val.map tz.2)),
          χ.continuous.comp (H.map.continuous.comp
            (continuous_fst.prodMk (d.val.embedded.continuous.comp continuous_snd)))⟩
        map_zero_left := by
          intro z
          change χ (H.map (⟨0,by norm_num⟩,d.val.map z))=A*z^k
          rw [H.at_zero]
          exact hparam z
        map_one_left := by intro z;rfl
      }
      refine ⟨f,⟨G⟩,?_⟩
      intro z hz w hw
      have hpoint (u : Circle) (hu : f u=θ) :
          H.finalMap (d.val.map u) ∈ c.val.image ∩ b.val.image := by
        constructor
        · rw [←hfiber]
          exact hu
        · rw [←hH]
          exact ⟨d.val.map u,mem_range_self u,rfl⟩
      have hh : H.finalMap (d.val.map z)=H.finalMap (d.val.map w) :=
        hcontact (hpoint z hz) (hpoint w hw)
      change H.map (⟨1,by norm_num⟩,d.val.map z)=H.map (⟨1,by norm_num⟩,d.val.map w) at hh
      rw [←he,←he] at hh
      exact d.val.embedded.injective (e.injective hh)
    have hLoopLift (k : ℤ) (a : Circle) (f : C(Circle,Circle))
        (H : (⟨fun z : Circle => a*z^k,by fun_prop⟩ : C(Circle,Circle)).Homotopy f) :
        ∃ F : C(unitInterval,ℝ),
          (∀ u : unitInterval, Circle.exp (F u)=f (Circle.exp (2*Real.pi*(u:ℝ)))) ∧
          F 1-F 0=(k:ℝ)*(2*Real.pi) := by
      obtain ⟨a₀,ha₀⟩ := Circle.exp_surjective a
      let γ : C(unitInterval,Circle) := ⟨fun u => Circle.exp (2*Real.pi*(u:ℝ)),by fun_prop⟩
      let G : C(unitInterval×unitInterval,Circle) := ⟨fun z => H (z.1,γ z.2),
        H.continuous.comp (continuous_fst.prodMk (γ.continuous.comp continuous_snd))⟩
      let F₀ : C(unitInterval,ℝ) := ⟨fun u => a₀+(k:ℝ)*(2*Real.pi*(u:ℝ)),by fun_prop⟩
      have hG₀ (u : unitInterval) : G (0,u)=Circle.exp (F₀ u) := by
        change H (0,γ u)=Circle.exp (a₀+(k:ℝ)*(2*Real.pi*(u:ℝ)))
        rw [H.apply_zero,Circle.exp_add,ha₀]
        apply congrArg (fun z : Circle => a*z)
        simpa only [γ,ContinuousMap.coe_mk,zsmul_eq_mul] using
          (Circle.exp_zsmul (2*Real.pi*(u:ℝ)) k).symm
      let L : C(unitInterval×unitInterval,ℝ) := Circle.isCoveringMap_exp.liftHomotopy G F₀ hG₀
      have hL (t u : unitInterval) : Circle.exp (L (t,u))=G (t,u) :=
        congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts G F₀ hG₀) (t,u)
      have hL₀ (u : unitInterval) : L (0,u)=F₀ u :=
        Circle.isCoveringMap_exp.liftHomotopy_zero G F₀ hG₀ u
      have hγ : γ 1=γ 0 := by simp [γ]
      have hloop (t : unitInterval) : G (t,1)=G (t,0) := by
        change H (t,γ 1)=H (t,γ 0)
        rw [hγ]
      let δ : C(unitInterval,Circle) := ⟨fun t => G (t,0),
        G.continuous.comp (continuous_id.prodMk continuous_const)⟩
      let A : C(unitInterval,ℝ) := ⟨fun t => L (t,0),
        L.continuous.comp (continuous_id.prodMk continuous_const)⟩
      let B : C(unitInterval,ℝ) := ⟨fun t => L (t,1)-(k:ℝ)*(2*Real.pi),by fun_prop⟩
      have hA : Circle.exp ∘ A=δ := by
        funext t
        exact hL t 0
      have hB : Circle.exp ∘ B=δ := by
        funext t
        change Circle.exp (L (t,1)-(k:ℝ)*(2*Real.pi))=G (t,0)
        rw [Circle.exp_sub,hL,Circle.exp_int_mul_two_pi,div_one,hloop]
      have hAB₀ : A 0=B 0 := by
        change L (0,0)=L (0,1)-(k:ℝ)*(2*Real.pi)
        rw [hL₀,hL₀]
        simp [F₀]
      have hAeq : A=Circle.isCoveringMap_exp.liftPath δ (A 0) (by
          simpa using (congrFun hA 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hA 0).symm)).mpr ⟨hA,rfl⟩
      have hBeq : B=Circle.isCoveringMap_exp.liftPath δ (A 0) (by
          simpa using (congrFun hA 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hA 0).symm)).mpr ⟨hB,hAB₀.symm⟩
      have hAB : A=B := hAeq.trans hBeq.symm
      let F : C(unitInterval,ℝ) := ⟨fun u => L (1,u),
        L.continuous.comp (continuous_const.prodMk continuous_id)⟩
      refine ⟨F,?_,?_⟩
      · intro u
        exact (hL 1 u).trans (H.apply_one (γ u))
      · have hh := congrArg (fun C : C(unitInterval,ℝ) => C 1) hAB
        change L (1,0)=L (1,1)-(k:ℝ)*(2*Real.pi) at hh
        change L (1,1)-L (1,0)=(k:ℝ)*(2*Real.pi)
        linarith
    have hLiftBound (F : C(unitInterval,ℝ)) (f : C(Circle,Circle)) (θ : Circle) (k : ℤ)
        (hF : ∀ u : unitInterval, Circle.exp (F u)=f (Circle.exp (2*Real.pi*(u:ℝ))))
        (hend : F 1-F 0=(k:ℝ)*(2*Real.pi))
        (hsub : {z : Circle | f z=θ}.Subsingleton) : k.natAbs ≤ 1 := by
      have hPositive (F : C(unitInterval,ℝ)) (f : C(Circle,Circle)) (θ : Circle) (k : ℤ)
          (hF : ∀ u : unitInterval, Circle.exp (F u)=f (Circle.exp (2*Real.pi*(u:ℝ))))
          (hend : F 1-F 0=(k:ℝ)*(2*Real.pi))
          (hsub : {z : Circle | f z=θ}.Subsingleton) : ¬ 2≤k := by
        intro hk
        have hP : 0 < 2*Real.pi := by positivity
        obtain ⟨r,hr⟩ := Circle.exp_surjective θ
        let j : ℤ := Int.floor ((F 0-r)/(2*Real.pi))+1
        let α : ℝ := r+(j:ℝ)*(2*Real.pi)
        have hlo : F 0<α := by
          have h := (div_lt_iff₀ hP).mp (Int.lt_floor_add_one ((F 0-r)/(2*Real.pi)))
          dsimp [α,j]
          push_cast
          linarith
        have hhi : α≤F 0+2*Real.pi := by
          have h := (le_div_iff₀ hP).mp (Int.floor_le ((F 0-r)/(2*Real.pi)))
          dsimp [α,j]
          push_cast
          linarith
        have hkR : (2:ℝ)≤k := by exact_mod_cast hk
        have hα1 : α≤F 1 := by nlinarith
        have hα2 : α+2*Real.pi≤F 1 := by nlinarith
        obtain ⟨u,hu⟩ := intermediate_value_univ (0:unitInterval) 1 F.continuous ⟨hlo.le,hα1⟩
        obtain ⟨v,hv⟩ := intermediate_value_univ (0:unitInterval) 1 F.continuous
          ⟨by linarith,hα2⟩
        have huPos : 0<(u:ℝ) := by
          by_contra h
          have he : u=0 := Subtype.ext (le_antisymm (not_lt.mp h) u.property.1)
          rw [he] at hu
          linarith
        have hvPos : 0<(v:ℝ) := by
          by_contra h
          have he : v=0 := Subtype.ext (le_antisymm (not_lt.mp h) v.property.1)
          rw [he] at hv
          linarith
        have hα : Circle.exp α=θ := by
          dsimp [α]
          rw [Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one,hr]
        have hαP : Circle.exp (α+2*Real.pi)=θ := by rw [Circle.exp_add_two_pi,hα]
        have huθ : f (Circle.exp (2*Real.pi*(u:ℝ)))=θ :=
          (hF u).symm.trans (hu ▸ hα)
        have hvθ : f (Circle.exp (2*Real.pi*(v:ℝ)))=θ :=
          (hF v).symm.trans (hv ▸ hαP)
        have he := hsub huθ hvθ
        obtain ⟨i,hi⟩ := Circle.exp_eq_exp.mp he
        have hiReal : (u:ℝ)=(v:ℝ)+(i:ℝ) := by
          apply mul_left_cancel₀ hP.ne'
          nlinarith
        have hiLo : (-1:ℝ) < i := by linarith [v.property.2]
        have hiHi : (i:ℝ)<1 := by linarith [u.property.2]
        have hiLoZ : (-1:ℤ) < i := by exact_mod_cast hiLo
        have hiHiZ : i<1 := by exact_mod_cast hiHi
        have hiZero : i=0 := by omega
        have huv : u=v := Subtype.ext (by simpa only [hiZero,Int.cast_zero,add_zero] using hiReal)
        rw [huv] at hu
        linarith
      have hkHi : k≤1 := by have h := hPositive F f θ k hF hend hsub;omega
      let F' : C(unitInterval,ℝ) := ⟨fun u => -(F u),by fun_prop⟩
      let f' : C(Circle,Circle) := ⟨fun z => (f z)⁻¹,by fun_prop⟩
      have hF' : ∀ u : unitInterval, Circle.exp (F' u)=f' (Circle.exp (2*Real.pi*(u:ℝ))) := by
        intro u
        change Circle.exp (-F u)=(f (Circle.exp (2*Real.pi*(u:ℝ))))⁻¹
        rw [Circle.exp_neg,hF]
      have hend' : F' 1-F' 0=((-k:ℤ):ℝ)*(2*Real.pi) := by
        change -(F 1)-(-(F 0))=((-k:ℤ):ℝ)*(2*Real.pi)
        push_cast
        linarith
      have hsub' : {z : Circle | f' z=θ⁻¹}.Subsingleton := by
        intro z hz w hw
        exact hsub (inv_injective hz) (inv_injective hw)
      have hkLo : -1≤k := by
        have h := hPositive F' f' θ⁻¹ (-k) hF' hend' hsub'
        omega
      have hkCases : k = -1 ∨ k = 0 ∨ k = 1 := by omega
      rcases hkCases with rfl|rfl|rfl <;> decide
    classical
    letI : ClosedSurface S := Classical.choice hS.2.1
    obtain ⟨Q,hQ,hQout⟩ := hCollapse S U hU p₀ e
    let χT : C(Torus,Circle) := ⟨fun x => x.1^(-n)*x.2^m,by fun_prop⟩
    let χ : C(S,Circle) := χT.comp Q
    have hfiber : {x : S | χ x=χT A}=c.val.image :=
      hExactFiber S U p₀ e Q hQ hQout a c.val hc A m n hg ha
    have hQB (z : Circle) : Q (d.val.map z)=B*torusWindingMap p q z := by
      rw [←hd z,hQ,e.apply_symm_apply]
      exact hb z
    have hmul (x y : Torus) : χT (x*y)=χT x*χT y := by
      dsimp [χT]
      simp only [Prod.fst_mul,Prod.snd_mul,mul_zpow]
      ac_rfl
    have hwind (z : Circle) : χT (torusWindingMap p q z)=z^(m*q-n*p) := by
      change (z^p)^(-n)*(z^q)^m=z^(m*q-n*p)
      rw [←zpow_mul,←zpow_mul,←zpow_add]
      congr 1
      ring
    have hparam (z : Circle) : χ (d.val.map z)=χT B*z^(m*q-n*p) := by
      change χT (Q (d.val.map z))=_
      rw [hQB,hmul,hwind]
    obtain ⟨f,⟨H⟩,hsub⟩ := hSourceCircle S hS c d χ (χT A) (χT B) (m*q-n*p)
      hfiber hparam hle
    obtain ⟨F,hF,hend⟩ := hLoopLift (m*q-n*p) (χT B) f H
    exact hLiftBound F f (χT A) (m*q-n*p) hF hend hsub
  have hDistinctSmallDeterminant (s t : FareySlope) (hne : s≠t)
      (hbound : Int.natAbs ((slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1)≤1) : FareyAdjacent s t := by
    have hZero (s t : FareySlope)
        (hzero : (slopeDirection s).1*(slopeDirection t).2-
          (slopeDirection s).2*(slopeDirection t).1=0) : s=t := by
      cases s with
      | none =>
        cases t with
        | none => rfl
        | some q => simp [slopeDirection] at hzero
      | some q =>
        cases t with
        | none => simp [slopeDirection] at hzero
        | some r =>
          congr 1
          have hq : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
          have hr : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_nz
          rw [←q.num_div_den,←r.num_div_den,div_eq_div_iff hq hr]
          have hz : q.num*(r.den:ℤ)=(q.den:ℤ)*r.num := sub_eq_zero.mp hzero
          exact_mod_cast hz.trans (mul_comm (q.den:ℤ) r.num)
    have hNZ : Int.natAbs ((slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1)≠0 := by
      intro hz
      exact hne (hZero s t (Int.natAbs_eq_zero.mp hz))
    have hOne : Int.natAbs ((slopeDirection s).1*(slopeDirection t).2-
        (slopeDirection s).2*(slopeDirection t).1)=1 := by omega
    cases s with
    | none =>
      cases t with
      | none => exact (hne rfl).elim
      | some q => simpa [FareyAdjacent,slopeDirection] using hOne
    | some p =>
      cases t with
      | none => simpa [FareyAdjacent,slopeDirection] using hOne
      | some q => simpa only [FareyAdjacent,slopeDirection,mul_comm] using hOne
  have hLowerU (s t : FareySlope) (hne : s≠t)
      (hle : geometricIntersection (vertex (.inl s)) (vertex (.inl t)) ≤ 1) :
      FareyAdjacent s t := by
    apply hDistinctSmallDeterminant s t hne
    exact hSourceLowerCount S hS U hU (1,1) eU (F s) (F t)
      ⟨GU s,hEssU s⟩ ⟨GU t,hEssU t⟩ (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (hPrimitive s) (hParam s) (hParam t) (fun _ => rfl) (fun _ => rfl) hle
  
  have hLowerV (s t : FareySlope) (hne : s≠t)
      (hle : geometricIntersection (vertex (.inr s)) (vertex (.inr t)) ≤ 1) :
      FareyAdjacent s t := by
    apply hDistinctSmallDeterminant s t hne
    exact hSourceLowerCount S hS V hV (1,1) eV (F s) (F t)
      ⟨GV s,hEssV s⟩ ⟨GV t,hEssV t⟩ (A s) (A t)
      (slopeDirection s).1 (slopeDirection s).2 (slopeDirection t).1 (slopeDirection t).2
      (hPrimitive s) (hParam s) (hParam t) (fun _ => rfl) (fun _ => rfl) hle
  
  have hLinkFareyFace (σ : Finset (Sum FareySlope FareySlope))
      (hlink : LinkFace geometricIntersection v.val (σ.image vertex)) : FareyJoinFace σ := by
    intro a ha b hb hne
    have hneV : vertex a≠vertex b := fun h => hne (hVertexInjective h)
    have hle : geometricIntersection (vertex a) (vertex b)≤1 := by
      apply hlink.2
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨a,ha,rfl⟩)
      · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b,hb,rfl⟩)
      · exact hneV
    cases a with
    | inl a =>
      cases b with
      | inl b => exact hLowerU a b (fun h => hne (congrArg Sum.inl h)) hle
      | inr b => trivial
    | inr a =>
      cases b with
      | inl b => trivial
      | inr b => exact hLowerV a b (fun h => hne (congrArg Sum.inr h)) hle
  have hNonseparatingFilledAdmissible (S : Type) [TopologicalSpace S] [T2Space S]
      (U : Set S) (hU : IsOpen U) (hOutside : ∃ x : S, x∉U)
      (p : Torus) (e : U ≃ₜ Punctured p)
      (b : Curve (Punctured p)) (d : Curve S) (hd : Essential d) (hNS : Nonseparating d)
      (hparam : ∀ z, (e.symm (b.map z)).val=d.map z) : Essential (fill b) := by
    have hCollapse (S : Type) [TopologicalSpace S] [T2Space S]
        (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p) :
        ∃ q : C(S,Torus), (∀ x : U, q x.val = (e x).val) ∧
          (∀ x, x ∉ U → q x = p) := by
      classical
      let q : S → Torus := fun x => if hx : x ∈ U then (e ⟨x,hx⟩).val else p
      have hqU (x : U) : q x.val=(e x).val := by simp [q,x.property]
      have hqOut (x : S) (hx : x ∉ U) : q x=p := by simp [q,hx]
      have hq : Continuous q := by
        apply continuous_def.mpr
        intro O hO
        by_cases hp : p ∈ O
        · let K : Set Torus := Oᶜ
          have hK : IsCompact K := hO.isClosed_compl.isCompact
          letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
          have hKp : ∀ x ∈ K, x ≠ p := by
            intro x hx he
            exact hx (he ▸ hp)
          let f : K → S := fun x => (e.symm ⟨x.val,hKp x.val x.property⟩).val
          have hf : Continuous f := continuous_subtype_val.comp
            (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _))
          have hr : IsCompact (range f) := isCompact_range hf
          have heq : q ⁻¹' O = (range f)ᶜ := by
            ext x
            constructor
            · intro hx
              rintro ⟨y,hy⟩
              have hxU : x ∈ U := hy ▸ (e.symm ⟨y.val,hKp y.val y.property⟩).property
              have hqv : q x=y.val := by
                rw [←hy,hqU]
                exact congrArg Subtype.val (e.apply_symm_apply _)
              exact y.property (hqv ▸ hx)
            · intro hx
              change q x ∈ O
              by_cases hxU : x ∈ U
              · rw [show q x=(e ⟨x,hxU⟩).val from hqU ⟨x,hxU⟩]
                by_contra hn
                apply hx
                refine ⟨⟨(e ⟨x,hxU⟩).val,hn⟩,?_⟩
                change (e.symm (e ⟨x,hxU⟩)).val=x
                rw [e.symm_apply_apply]
              · rw [hqOut x hxU]
                exact hp
          rw [heq]
          exact hr.isClosed.isOpen_compl
        · have heq : q ⁻¹' O = Subtype.val ''
              ((fun x : U => (e x).val) ⁻¹' O) := by
            ext x
            constructor
            · intro hx
              have hxU : x ∈ U := by
                by_contra hn
                exact hp ((hqOut x hn) ▸ hx)
              refine ⟨⟨x,hxU⟩,?_,rfl⟩
              change (e ⟨x,hxU⟩).val ∈ O
              change q x ∈ O at hx
              rw [hqU ⟨x,hxU⟩] at hx
              exact hx
            · rintro ⟨y,hy,rfl⟩
              change q y.val ∈ O
              change (e y).val ∈ O at hy
              rw [hqU y]
              exact hy
          rw [heq]
          exact hU.isOpenMap_subtype_val _ (hO.preimage
            (continuous_subtype_val.comp e.continuous))
      exact ⟨⟨q,hq⟩,hqU,hqOut⟩
    have hDiskInterior (S : Type) [TopologicalSpace S] (U : Set S)
        (p : Torus) (e : U ≃ₜ Punctured p)
        (c : Curve S) (hc : Essential c) (d : Curve (Punctured p))
        (hparam : ∀ z, (e.symm (d.map z)).val=c.map z)
        (f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus))
        (hf : IsEmbedding f)
        (hboundary : f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} = (fill d).image) :
        ∃ x, f x=p ∧ (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1 := by
      have hcontain : p ∈ range f := by
        classical
        by_contra havoid
        have hav (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) : f x ≠ p := by
          intro hx
          exact havoid ⟨x,hx⟩
        let fp : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Punctured p) :=
          ⟨fun x => ⟨f x,hav x⟩,f.continuous.subtype_mk _⟩
        have hfp : IsEmbedding fp := by
          apply (IsEmbedding.of_comp_iff (g := Subtype.val) IsEmbedding.subtypeVal).mp
          exact hf
        let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
          ⟨fun x => (e.symm (fp x)).val,
            continuous_subtype_val.comp (e.symm.continuous.comp fp.continuous)⟩
        apply hc
        refine ⟨g,IsEmbedding.subtypeVal.comp (e.symm.isEmbedding.comp hfp),?_⟩
        ext x
        constructor
        · rintro ⟨y,hy,rfl⟩
          have hb : f y ∈ (fill d).image := hboundary ▸ ⟨y,hy,rfl⟩
          obtain ⟨z,hz⟩ := hb
          have he : d.map z=fp y := Subtype.ext hz
          refine ⟨z,?_⟩
          rw [←hparam z,he]
          rfl
        · rintro ⟨z,rfl⟩
          have hz : (d.map z).val ∈ (fill d).image := mem_range_self z
          rw [←hboundary] at hz
          obtain ⟨y,hy,hyz⟩ := hz
          refine ⟨y,hy,?_⟩
          change (e.symm (fp y)).val=c.map z
          have he : fp y=d.map z := Subtype.ext hyz
          rw [he,hparam z]
      obtain ⟨x,hx⟩ := hcontain
      have hnot : (x : EuclideanSpace ℝ (Fin 2)) ∉ Metric.sphere 0 1 := by
        intro hs
        have hb : p ∈ (fill d).image := hboundary ▸ ⟨x,hs,hx⟩
        obtain ⟨z,hz⟩ := hb
        exact (d.map z).property hz
      refine ⟨x,hx,?_⟩
      rw [Metric.mem_ball]
      have hle := x.property
      rw [Metric.mem_closedBall] at hle
      have hne : dist (x : EuclideanSpace ℝ (Fin 2)) 0 ≠ 1 := by
        simpa only [Metric.mem_sphere] using hnot
      exact lt_of_le_of_ne hle hne
    have hPowerZero (k : ℤ)
        (h : (⟨fun z : Circle => z ^ k, continuous_zpow k⟩ : C(Circle, Circle)).Nullhomotopic) :
        k = 0 := by
      obtain ⟨r, ⟨H⟩⟩ := h
      obtain ⟨r₀, hr₀⟩ := Circle.exp_surjective r
      let G := H.symm
      let L : C(unitInterval × Circle, ℝ) := Circle.isCoveringMap_exp.liftHomotopy
        G.toContinuousMap (ContinuousMap.const Circle r₀)
        (fun z => (G.apply_zero z).trans hr₀.symm)
      have hL (t : unitInterval) (z : Circle) : Circle.exp (L (t, z)) = G (t, z) :=
        congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts G.toContinuousMap
          (ContinuousMap.const Circle r₀) _) (t, z)
      let F : C(Circle, ℝ) := ⟨fun z => L (1, z), L.continuous.comp
        (continuous_const.prodMk continuous_id)⟩
      have hF (z : Circle) : Circle.exp (F z) = z ^ k :=
        (hL 1 z).trans (G.apply_one z)
      let γ : C(unitInterval, Circle) :=
        ⟨fun t => Circle.exp (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      let δ : C(unitInterval, Circle) := ⟨fun t => (γ t) ^ k, (continuous_zpow k).comp γ.continuous⟩
      let Γ : C(unitInterval, ℝ) := F.comp γ
      let Λ : C(unitInterval, ℝ) := ⟨fun t => Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ)), by fun_prop⟩
      have hΓlift : Circle.exp ∘ Γ = δ := by
        funext t
        exact hF (γ t)
      have hΛlift : Circle.exp ∘ Λ = δ := by
        funext t
        change Circle.exp (Γ 0 + (k : ℝ) * (2 * Real.pi * (t : ℝ))) = (γ t) ^ k
        rw [Circle.exp_add]
        have hΓ0 : Circle.exp (Γ 0) = 1 := by
          have hh := congrFun hΓlift 0
          simpa [δ, γ] using hh
        rw [hΓ0, one_mul]
        simpa only [zsmul_eq_mul, γ, ContinuousMap.coe_mk] using
          Circle.exp_zsmul (2 * Real.pi * (t : ℝ)) k
      have hΓ0 : Γ 0 = Λ 0 := by simp [Λ]
      have hΓeq : Γ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΓlift, rfl⟩
      have hΛeq : Λ = Circle.isCoveringMap_exp.liftPath δ (Γ 0) (by
          simpa using (congrFun hΓlift 0).symm) :=
        (Circle.isCoveringMap_exp.eq_liftPath_iff' (by
          simpa using (congrFun hΓlift 0).symm)).mpr ⟨hΛlift, hΓ0.symm⟩
      have hend : Γ 1 = Λ 1 := by rw [hΓeq, hΛeq]
      have hloop : Γ 1 = Γ 0 := by
        change F (γ 1) = F (γ 0)
        congr 1
        simp [γ]
      rw [hloop] at hend
      have he : (k : ℝ) * (2 * Real.pi) = 0 := by
        have hh : Γ 0 = Γ 0 + (k : ℝ) * (2 * Real.pi) := by simpa [Λ] using hend
        linarith
      have hk : (k : ℝ) = 0 := (mul_eq_zero.mp he).resolve_right
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      exact_mod_cast hk
    have hDiskProper
        (f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus))
        (hf : IsEmbedding f) : (range f)ᶜ.Nonempty := by
      classical
      by_contra h
      have hRange : range f=univ := by
        apply eq_univ_of_forall
        intro x
        by_contra hx
        exact h ⟨x,hx⟩
      letI : ContractibleSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
        Metric.contractibleSpace_closedBall (by norm_num)
      let E := (hf.toHomeomorph.trans (Homeomorph.setCongr hRange)).trans (Homeomorph.Set.univ Torus)
      letI : ContractibleSpace Torus := E.symm.contractibleSpace
      let β : C(Circle,Torus) := ⟨fun z => (z,1),by fun_prop⟩
      let π : C(Torus,Circle) := ⟨Prod.fst,continuous_fst⟩
      have hnull := ((id_nullhomotopic Torus).comp_left β).comp_right π
      have hone : (⟨fun z : Circle => z^(1:ℤ),continuous_zpow _⟩ : C(Circle,Circle)).Nullhomotopic := by
        have heq : π.comp ((ContinuousMap.id Torus).comp β)=
            (⟨fun z : Circle => z^(1:ℤ),continuous_zpow _⟩ : C(Circle,Circle)) := by
          apply ContinuousMap.ext
          intro z
          simp [π,β]
        rw [heq] at hnull
        exact hnull
      have hh := hPowerZero 1 hone
      norm_num at hh
    classical
    obtain ⟨Q,hQ,hQout⟩ := hCollapse S U hU p e
    intro ⟨f,hf,hboundary⟩
    obtain ⟨x,hxp,hxInt⟩ := hDiskInterior S U p e d hd b hparam f hf hboundary
    let D := f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
      (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.ball 0 1}
    have hpD : p∈D := ⟨x,hxInt,hxp⟩
    obtain ⟨C,hClosed⟩ := actual_standard_torus_has_closed_surface_structure
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) Torus := C
    have hDopen : IsOpen D := embedded_disk_interior_isOpen f hf
    letI : CompactSpace (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1) :=
      isCompact_iff_compactSpace.mp (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
    have hRclosed : IsClosed (range f) := (isCompact_range f.continuous).isClosed
    have hpartition : range f=D ∪ (fill b).image := by
      rw [embedded_disk_range_partition,hboundary]
      rfl
    have hDdis : Disjoint D (fill b).image := by
      apply disjoint_left.mpr
      rintro y ⟨u,hu,rfl⟩ hy
      rw [←hboundary] at hy
      obtain ⟨v,hv,he⟩ := hy
      have huv : v=u := hf.injective he
      rw [huv] at hv
      change dist (u : EuclideanSpace ℝ (Fin 2)) 0=1 at hv
      change dist (u : EuclideanSpace ℝ (Fin 2)) 0<1 at hu
      linarith
    have hBoundaryFiber (y : S) : Q y∈(fill b).image ↔ y∈d.image := by
      constructor
      · rintro ⟨z,hz⟩
        have hyU : y∈U := by
          by_contra h
          rw [hQout y h] at hz
          exact (b.map z).property hz
        have hbEq : b.map z=e ⟨y,hyU⟩ := Subtype.ext (hz.trans (hQ ⟨y,hyU⟩))
        refine ⟨z,?_⟩
        rw [←hparam z,hbEq,e.symm_apply_apply]
      · rintro ⟨z,rfl⟩
        rw [←hparam z,hQ,e.apply_symm_apply]
        exact ⟨z,rfl⟩
    let A := Q ⁻¹' D
    let B := Q ⁻¹' (range f)ᶜ
    have hA : IsOpen A := hDopen.preimage Q.continuous
    have hB : IsOpen B := hRclosed.isOpen_compl.preimage Q.continuous
    have hAB : Disjoint A B := by
      apply disjoint_left.mpr
      intro y hyA hyB
      exact hyB (hpartition.symm ▸ Or.inl hyA)
    have hcover : A ∪ B=d.imageᶜ := by
      ext y
      constructor
      · intro hy hyd
        have hbd := (hBoundaryFiber y).mpr hyd
        rcases hy with hy|hy
        · exact disjoint_left.mp hDdis hy hbd
        · exact hy (hpartition.symm ▸ Or.inr hbd)
      · intro hy
        by_cases hyR : Q y∈range f
        · rw [hpartition] at hyR
          rcases hyR with hyD|hyBd
          · exact Or.inl hyD
          · exact False.elim (hy ((hBoundaryFiber y).mp hyBd))
        · exact Or.inr hyR
    have hANonempty : A.Nonempty := by
      obtain ⟨y,hy⟩ := hOutside
      exact ⟨y,by change Q y∈D;rw [hQout y hy];exact hpD⟩
    have hBNonempty : B.Nonempty := by
      obtain ⟨y,hy⟩ := hDiskProper f hf
      have hyP : y≠p := by
        intro h
        exact hy (hpartition.symm ▸ Or.inl (h ▸ hpD))
      refine ⟨(e.symm ⟨y,hyP⟩).val,?_⟩
      change Q (e.symm ⟨y,hyP⟩).val∉range f
      rw [hQ,e.apply_symm_apply]
      exact hy
    have hsides : d.imageᶜ ⊆ A ∨ d.imageᶜ ⊆ B :=
      hNS.isPreconnected.subset_or_subset hA hB hAB (hcover ▸ Subset.rfl)
    rcases hsides with hsides|hsides
    · obtain ⟨y,hy⟩ := hBNonempty
      exact disjoint_left.mp hAB (hsides (hcover ▸ Or.inr hy)) hy
    · obtain ⟨y,hy⟩ := hANonempty
      exact disjoint_left.mp hAB hy (hsides (hcover ▸ Or.inl hy))
  refine ⟨{
    vertex := vertex
    vertex_link := hVertexLink
    vertex_injective := hVertexInjective
    vertex_surjective := ?_
    face_iff := ?_
  }⟩
  · intro w hw
    obtain ⟨d,hd,hdis,hsides⟩ := hactualSide w hw
    have hwNS : nonseparatingVertex w := by
      by_contra hn
      have hwSep : IsSeparatingVertex S w :=
        (separatingVertex_iff_not_nonseparatingVertex S w).mpr hn
      have hvw : v.val≠w := by simpa using hw.1
      have hgt := hsep v.val w v.property hwSep hvw
      have hz := hlinkZero w hw
      omega
    have hdNS : Nonseparating d.val := by
      change nonseparatingVertex (Quotient.mk (essentialCurveSetoid S) d)
      rw [hd]
      exact hwNS
    rcases hsides with hside|hside
    · obtain ⟨b,hb⟩ := hPuncturedRepresentative U (1,1) eU d.val hside
      have hDiskContainsPuncture := hFilledDiskInterior S U (1,1) eU d.val d.property b hb
      have hne : Quotient.mk (essentialCurveSetoid S) d ≠ Quotient.mk (essentialCurveSetoid S) c := by
        intro he
        have hvw : v.val=w := hcv.symm.trans (he.symm.trans hd)
        exact hw.1 (by simp [hvw])
      have hOutside : ∃ x : S, x∉U := by
        refine ⟨c.val.map (1 : Circle),?_⟩
        intro hx
        have hh : c.val.map (1 : Circle)∈c.val.imageᶜ := hcover ▸ Or.inl hx
        exact hh (mem_range_self (1 : Circle))
      have hbAdm : Admissible b := hNonseparatingFilledAdmissible S U hU
        hOutside (1,1) eU b d.val d.property hdNS hb
      obtain ⟨s,hbFs,hunique⟩ := hClass b hbAdm
      have hSupported : ∃ (H : AmbientIsotopy (Punctured (1,1))) (K : Set (Punctured (1,1))),
          IsCompact K ∧ (∀ t x, x ∉ K → H.map (t,x)=x) ∧ H.finalMap '' b.image=(F s).image :=
        hCompactLocalized b (F s) hbFs
      obtain ⟨H,K,hK,hFix,hH⟩ := hSupported
      have hSourceClass : AmbientIsotopy.Rel d.val.image (GU s).image :=
        hSupportedClassTransport S U hU (1,1) eU b (F s) d.val (GU s)
          hb (fun _ => rfl) H K hK hFix hH
      refine ⟨Sum.inl s,?_⟩
      exact (Quotient.sound hSourceClass).symm.trans hd
    · obtain ⟨b,hb⟩ := hPuncturedRepresentative V (1,1) eV d.val hside
      have hDiskContainsPuncture := hFilledDiskInterior S V (1,1) eV d.val d.property b hb
      have hne : Quotient.mk (essentialCurveSetoid S) d ≠ Quotient.mk (essentialCurveSetoid S) c := by
        intro he
        have hvw : v.val=w := hcv.symm.trans (he.symm.trans hd)
        exact hw.1 (by simp [hvw])
      have hOutside : ∃ x : S, x∉V := by
        refine ⟨c.val.map (1 : Circle),?_⟩
        intro hx
        have hh : c.val.map (1 : Circle)∈c.val.imageᶜ := hcover ▸ Or.inr hx
        exact hh (mem_range_self (1 : Circle))
      have hbAdm : Admissible b := hNonseparatingFilledAdmissible S V hV
        hOutside (1,1) eV b d.val d.property hdNS hb
      obtain ⟨s,hbFs,hunique⟩ := hClass b hbAdm
      have hSupported : ∃ (H : AmbientIsotopy (Punctured (1,1))) (K : Set (Punctured (1,1))),
          IsCompact K ∧ (∀ t x, x ∉ K → H.map (t,x)=x) ∧ H.finalMap '' b.image=(F s).image :=
        hCompactLocalized b (F s) hbFs
      obtain ⟨H,K,hK,hFix,hH⟩ := hSupported
      have hSourceClass : AmbientIsotopy.Rel d.val.image (GV s).image :=
        hSupportedClassTransport S V hV (1,1) eV b (F s) d.val (GV s)
          hb (fun _ => rfl) H K hK hFix hH
      refine ⟨Sum.inr s,?_⟩
      exact (Quotient.sound hSourceClass).symm.trans hd
  · intro σ
    constructor
    · exact hLinkFareyFace σ
    · exact hFareyFaceLink σ

theorem nonseparating_strongDeformationRetract_genusTwo
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
    (hS : IsGenus S 2) :
    IsStrongDeformationRetract (NonseparatingLocus S) := by
  classical
  letI : DecidableEq (Vertex S) := Classical.decEq _
  -- Independently owned original separating-nonadjacency provider.
  have hsep : ∀ a b : Vertex S, IsSeparatingVertex S a →
      IsSeparatingVertex S b → a ≠ b → 1 < geometricIntersection a b := by
    exact source_genus_two_separating_vertices_nonadjacent S hS
  let d : ∀ v : {u : Vertex S // IsSeparatingVertex S u},
      FareyJoinLinkDictionary (curveComplex S 1) geometricIntersection v.1 :=
    fun v => Classical.choice (source_genus_two_separating_farey_dictionary S hS v)
  change IsStrongDeformationRetract
    (NonseparatingWeightLocus (curveComplex S 1) (IsSeparatingVertex S))
  apply farey_dictionary_star_deletion_consumer (curveComplex S 1)
    geometricIntersection (IsSeparatingVertex S) _ _ hsep d
  · intro σ hσ
    exact hσ.2
  · intro σ hne hσ
    exact ⟨hne,hσ⟩
end CurveComplexGenusTwo.SourceTopology
#print axioms CurveComplexGenusTwo.SourceTopology.source_genus_two_separating_farey_dictionary
#print axioms CurveComplexGenusTwo.SourceTopology.nonseparating_strongDeformationRetract_genusTwo
