import CurveComplexGenusTwo.Topology.ActualSeparatingNonadjacency.ActualOriginalPunctureContainingDiskBoundaryParallelProof
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualOriginalClassificationStatements
import CurveComplexGenusTwo.Topology.PrimitiveEssential
import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualCircleProjectionEssential
import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12FullConnectivity
import CurveComplexGenusTwo.Topology.ActualGenusTwoRecognition.OriginalGenusTwoSeparatingActualCut
import CurveComplexGenusTwo.Topology.CurveCombinatorics
set_option maxHeartbeats 8000000
set_option maxRecDepth 7000
set_option backward.isDefEq.respectTransparency false
namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex CurveComplexGenusTwo.Topology CurveComplexGenusTwo.Topology.PuncturedTorusCandidate Set _root_.Topology Schoenflies CategoryTheory CategoryTheory.Limits
open CurveComplexGenusTwo.CWHurewicz
open scoped Manifold
theorem source_genus_two_separating_vertices_nonadjacent
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2) :
    ∀ a b : Vertex S, IsSeparatingVertex S a → IsSeparatingVertex S b →
      a ≠ b → 1 < geometricIntersection a b := by
  have hsmall (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (a b : Vertex S) (ha : IsSeparatingVertex S a)
      (hle : geometricIntersection a b ≤ 1) : geometricIntersection a b = 0 := by
    classical
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
    by_contra hzero
    have hone : geometricIntersection a b = 1 := by omega
    obtain ⟨c,d,hc,hd,ht,hcard⟩ := source_geometric_intersection_attained S a b
    have hcns : Nonseparating c.val := hOneCrossing c.val d.val ht (hcard.trans hone)
    obtain ⟨e,he,hdisc⟩ := ha
    have hrel : (essentialCurveSetoid S).r c e := Quotient.exact (hc.trans he.symm)
    exact hdisc ((nonseparating_isotopy_invariant hrel).mp hcns)
  have hfixed (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (c : EssentialCurve S) (w : Vertex S)
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
  have hside (S : Type) [TopologicalSpace S]
      [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
      (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p)
      (d : EssentialCurve S) (hsep : ¬ IsConnected d.val.imageᶜ)
      (hinside : ∀ z, d.val.map z ∈ U) :
      ∃ f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus),
        IsEmbedding f ∧
        f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} =
            Set.range (fun z => (e ⟨d.val.map z,hinside z⟩).val) ∧
        ∃ x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,
          ‖x.val‖<1 ∧ f x=p := by
    have hfilled (S : Type) [TopologicalSpace S]
        [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
        (U : Set S) (hU : IsOpen U) (p : Torus) (e : U ≃ₜ Punctured p)
        (d : EssentialCurve S) (hsep : ¬ IsConnected d.val.imageᶜ)
        (hinside : ∀ z, d.val.map z ∈ U) :
        let dT : Curve Torus := {
          map := fun z => (e ⟨d.val.map z,hinside z⟩).val
          embedded := IsEmbedding.subtypeVal.comp (e.isEmbedding.comp (d.val.embedded.codRestrict U hinside)) }
        BoundsDisc dT := by
      classical
      letI : ClosedSurface S := Classical.choice hS.2.1
      have hcollapse (S : Type) [TopologicalSpace S] [T2Space S]
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
      let dT : Curve Torus := {
        map := fun z => (e ⟨d.val.map z,hinside z⟩).val
        embedded := IsEmbedding.subtypeVal.comp (e.isEmbedding.comp (d.val.embedded.codRestrict U hinside)) }
      change BoundsDisc dT
      by_contra hnot
      have hess : Essential dT := hnot
      obtain ⟨m,n,hnonzero,hgcd,hhom⟩ := essential_torus_curve_has_primitive_winding dT hess
      obtain ⟨q,hq,hqOut⟩ := hcollapse S U hU p e
      let u := Int.gcdA m n
      let v := Int.gcdB m n
      have hbez : m*u+n*v=1 := by
        have h := Int.gcd_eq_gcd_ab m n
        rw [hgcd] at h
        exact h.symm
      let χ : C(Torus,Circle) := ⟨fun w => w.1^u*w.2^v,by fun_prop⟩
      have hwinding : χ.comp ⟨torusWindingMap m n,continuous_torusWindingMap m n⟩=ContinuousMap.id Circle := by
        apply ContinuousMap.ext
        intro z
        change (z^m)^u*(z^n)^v=z
        rw [←zpow_mul,←zpow_mul,←zpow_add,hbez,zpow_one]
      let dmap : C(Circle,S) := ⟨d.val.map,d.val.embedded.continuous⟩
      have hqmap : q.comp dmap=⟨dT.map,dT.embedded.continuous⟩ := by
        apply ContinuousMap.ext
        intro z
        exact hq ⟨d.val.map z,hinside z⟩
      have hloop : ((χ.comp q).comp dmap).Homotopic (ContinuousMap.id Circle) := by
        rw [ContinuousMap.comp_assoc,hqmap,←hwinding]
        exact (ContinuousMap.Homotopic.refl χ).comp hhom
      obtain ⟨collar,hcollar,hcore⟩ := LocalSurgery.actual_original_essential_circle_has_annular_collar
        S 2 (by omega) hS d
      have hz := source_separating_curve_actual_annular_fundamental_zero S hS d.val hsep collar hcollar hcore
      let F := (AlgebraicTopology.singularHomologyFunctor (ModuleCat.{0} ℤ) 1).obj (ModuleCat.of ℤ ℤ)
      have hloopMap : F.map (TopCat.ofHom ((χ.comp q).comp dmap))=𝟙 (F.obj (TopCat.of Circle)) := by
        have HH : TopCat.Homotopy (TopCat.ofHom ((χ.comp q).comp dmap)) (𝟙 (TopCat.of Circle)) := hloop.some
        have hh := TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor HH (ModuleCat.of ℤ ℤ) 1
        exact hh.trans (F.map_id _)
      have heq : TopCat.ofHom ((χ.comp q).comp dmap)=TopCat.ofHom dmap ≫ TopCat.ofHom (χ.comp q) := rfl
      rw [heq,F.map_comp] at hloopMap
      have hclass := congrArg (fun k => k CircleFundamentalCycle.fundamentalClass) hloopMap
      change F.map (TopCat.ofHom (χ.comp q)) (F.map (TopCat.ofHom dmap) CircleFundamentalCycle.fundamentalClass)=CircleFundamentalCycle.fundamentalClass at hclass
      change F.map (TopCat.ofHom dmap) CircleFundamentalCycle.fundamentalClass=0 at hz
      rw [hz,map_zero] at hclass
      have hcoord := CircleFundamentalCycle.fundamentalClass_coordinate
      rw [←hclass,map_zero] at hcoord
      norm_num at hcoord
    have hcontains (S : Type) [TopologicalSpace S] (U : Set S) (p : Torus) (e : U ≃ₜ Punctured p)
        (d : EssentialCurve S) (hinside : ∀ z, d.val.map z ∈ U)
        (dT : Curve Torus) (hmap : ∀ z, dT.map z=(e ⟨d.val.map z,hinside z⟩).val)
        (f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus))
        (hf : IsEmbedding f)
        (hb : f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1}=dT.image) :
        p ∈ Set.range f := by
      by_contra hp
      have hfp (x) : f x ≠ p := by
        intro he
        exact hp ⟨x,he⟩
      let g : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,S) :=
        ⟨fun x => (e.symm ⟨f x,hfp x⟩).val,
          continuous_subtype_val.comp (e.symm.continuous.comp (f.continuous.subtype_mk _))⟩
      have hg : IsEmbedding g := IsEmbedding.subtypeVal.comp
        (e.symm.isEmbedding.comp (hf.codRestrict {z : Torus | z ≠ p} hfp))
      apply d.property
      refine ⟨g,hg,?_⟩
      ext y
      constructor
      · rintro ⟨x,hx,rfl⟩
        have hxT : f x ∈ dT.image := hb ▸ ⟨x,hx,rfl⟩
        obtain ⟨w,hw⟩ := hxT
        refine ⟨w,?_⟩
        have heq : (⟨f x,hfp x⟩ : Punctured p)=e ⟨d.val.map w,hinside w⟩ := by
          apply Subtype.ext
          exact hw.symm.trans (hmap w)
        change d.val.map w=(e.symm ⟨f x,hfp x⟩).val
        rw [heq,e.symm_apply_apply]
      · rintro ⟨w,rfl⟩
        have hw : dT.map w ∈ f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
          (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1} := hb.symm ▸ ⟨w,rfl⟩
        obtain ⟨x,hx,hfx⟩ := hw
        refine ⟨x,hx,?_⟩
        have heq : (⟨f x,hfp x⟩ : Punctured p)=e ⟨d.val.map w,hinside w⟩ := by
          apply Subtype.ext
          exact hfx.trans (hmap w)
        change (e.symm ⟨f x,hfp x⟩).val=d.val.map w
        rw [heq,e.symm_apply_apply]
    let dT : Curve Torus := {
      map := fun z => (e ⟨d.val.map z,hinside z⟩).val
      embedded := IsEmbedding.subtypeVal.comp (e.isEmbedding.comp (d.val.embedded.codRestrict U hinside)) }
    obtain ⟨f,hf,hb⟩ := hfilled S hS U hU p e d hsep hinside
    obtain ⟨x,hxp⟩ := hcontains S U p e d hinside dT (fun _ => rfl) f hf hb
    refine ⟨f,hf,hb,x,?_,hxp⟩
    have hxle : ‖x.val‖≤1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
    have hxne : ‖x.val‖≠1 := by
      intro hnorm
      have hxboundary : x.val ∈ Metric.sphere (0:EuclideanSpace ℝ (Fin 2)) 1 := by
        simpa [Metric.mem_sphere,dist_zero_right] using hnorm
      have hpd : p ∈ dT.image := hb ▸ ⟨x,hxboundary,hxp⟩
      obtain ⟨w,hw⟩ := hpd
      exact (e ⟨d.val.map w,hinside w⟩).property hw
    exact lt_of_le_of_ne hxle hxne
  classical
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hBoundary (c d : EssentialCurve S)
      (U V : Set S) (hU : IsOpen U) (hV : IsOpen V)
      (hUV : Disjoint U V) (hcover : U ∪ V=c.val.imageᶜ)
      (hfrontU : frontier U=c.val.image) (hfrontV : frontier V=c.val.image)
      (e : U ≃ₜ Punctured (1,1)) (hinside : ∀ z, d.val.map z ∈ U)
      (f : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1,Torus))
      (hf : IsEmbedding f)
      (hb : f '' {x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 |
        (x : EuclideanSpace ℝ (Fin 2)) ∈ Metric.sphere 0 1}=
          Set.range (fun z => (e ⟨d.val.map z,hinside z⟩).val))
      (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1)
      (hx : ‖x.val‖<1) (hp : f x=(1,1)) :
      AmbientIsotopy.Rel c.val.image d.val.image := by
    exact actual_original_puncture_containing_disk_boundary_parallel S hS c d U V hU hV
      hUV hcover hfrontU hfrontV e hinside f hf hb x hx hp
  have hRigid (c d : EssentialCurve S) (hc : ¬ IsConnected c.val.imageᶜ)
      (hd : ¬ IsConnected d.val.imageᶜ) (hdis : Disjoint c.val.image d.val.image) :
      AmbientIsotopy.Rel c.val.image d.val.image := by
    obtain ⟨U,V,hU,hV,hUV,hcover,hfrontU,hfrontV,⟨eU⟩,⟨eV⟩⟩ :=
      source_genus_two_separating_actual_cut S hS c.val c.property hc
    have hsub : d.val.image ⊆ c.val.imageᶜ := by
      intro y hy hcy
      exact Set.disjoint_left.mp hdis hcy hy
    have hconn : IsConnected d.val.image := isConnected_range d.val.embedded.continuous
    have hloc : d.val.image ⊆ U ∨ d.val.image ⊆ V :=
      hconn.isPreconnected.subset_or_subset hU hV hUV (hcover.symm ▸ hsub)
    rcases hloc with hloc | hloc
    · have hinside : ∀ z, d.val.map z ∈ U := fun z => hloc ⟨z,rfl⟩
      obtain ⟨f,hf,hb,x,hx,hp⟩ := hside S hS U hU (1,1) eU d hd hinside
      exact hBoundary c d U V hU hV hUV hcover hfrontU hfrontV eU hinside f hf hb x hx hp
    · have hinside : ∀ z, d.val.map z ∈ V := fun z => hloc ⟨z,rfl⟩
      obtain ⟨f,hf,hb,x,hx,hp⟩ := hside S hS V hV (1,1) eV d hd hinside
      exact hBoundary c d V U hV hU hUV.symm (by simpa [union_comm] using hcover)
        hfrontV hfrontU eV hinside f hf hb x hx hp
  intro a b ha hb hab
  by_contra hle
  have hzero := hsmall S hS a b ha (by omega)
  obtain ⟨c,hc,hcsep⟩ := ha
  obtain ⟨d,hd,hdis⟩ := hfixed S hS c b (by rwa [hc])
  have hdsep : ¬ IsConnected d.val.imageᶜ := by
    obtain ⟨d',hd',hsep⟩ := hb
    have heq : Quotient.mk (essentialCurveSetoid S) d'=Quotient.mk (essentialCurveSetoid S) d := hd'.trans hd.symm
    have hrel := Quotient.exact heq
    exact fun hconn => hsep ((nonseparating_isotopy_invariant hrel).mpr hconn)
  exact hab (hc.symm.trans ((Quotient.sound (hRigid c d hcsep hdsep hdis)).trans hd))
end CurveComplexGenusTwo.SourceTopology
