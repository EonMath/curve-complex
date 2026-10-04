import CurveComplexGenusTwo.Topology.ActualConnectivity.ActualMain12NonseparatingSeed
import CurveComplexGenusTwo.Topology.ActualConnectivity.CanonicalSourceNonseparatingPointPaths
import CurveComplexGenusTwo.Topology.IntersectionParity.AxisChart
namespace CurveComplex
open Set Topology Schoenflies
-- Exact original disjoint-neighbor endpoint in ephemeral proof search.
theorem source_genus_two_separating_curve_disjoint_nonseparating
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (c : EssentialCurve S) (hc : ¬ Nonseparating c.val) :
    ∃ d : EssentialCurve S, Nonseparating d.val ∧
      Disjoint c.val.image d.val.image := by
  classical
  let : ClosedSurface S := Classical.choice hS.2.1
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
  let cv : Vertex S := Quotient.mk (essentialCurveSetoid S) c
  have reach (n : ℕ) : ∀ (β : {v : Vertex S // nonseparatingVertex v}),
      geometricIntersection β.val cv = n →
      ∃ γ : {v : Vertex S // nonseparatingVertex v}, geometricIntersection γ.val cv = 0 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro β hcount
      by_cases hz : n = 0
      · exact ⟨β,hcount.trans hz⟩
      obtain ⟨a,b,ha,hb,ht,hmin⟩ := source_geometric_intersection_attained S cv β.val
      have hbns : Nonseparating b.val := by
        have hn := β.property
        rw [← hb] at hn
        exact hn
      have hac : AmbientIsotopy.Rel a.val.image c.val.image := Quotient.exact ha
      have hcard : ht.1.toFinset.card = n := by
        rw [hmin,geometricIntersection_symm_of_chart cv β.val,hcount]
      by_cases hone : n = 1
      · have hans := hOneCrossing a.val b.val ht (hcard.trans hone)
        exact (hc ((nonseparating_isotopy_invariant (a:=a) (b:=c) hac).mp hans)).elim
      have hlarge : 1 < ht.1.toFinset.card := by omega
      obtain ⟨u,v,hu,hv,huv⟩ := Finset.one_lt_card_iff.mp hlarge
      have hu' : u ∈ a.val.image ∩ b.val.image := by simpa using hu
      have hv' : v ∈ a.val.image ∩ b.val.image := by simpa using hv
      obtain ⟨w,huw,hw,f,g,hf,hg,hf0,hg0,hf1,hg1,hfa,hgb,havoid,hmeet,raw,hraw,hcompact⟩ :=
        LocalSurgery.source_two_curve_first_return_boundary a.val b.val ht u v hu' hv' huv
      let D : SourceFirstReturnBoundary a.val b.val := {
        start := u,finish := w,distinct := huw,start_mem := hu',finish_mem := hw,
        first := f,second := g,first_embedded := hf,second_embedded := hg,
        first_zero := hf0,second_zero := hg0,first_one := hf1,second_one := hg1,
        first_subset := hfa,second_subset := hgb,first_interior_avoids := havoid,
        intersection := hmeet,boundary := raw,boundary_image := hraw,boundary_compact := hcompact }
      obtain ⟨B⟩ := source_first_return_two_surgery_branches D
      obtain ⟨i,hnsraw⟩ := source_genus_two_theta_nonseparating_retention S hS D B hbns
      obtain ⟨d,hrel,hbd,had,hbdcount,hadcount⟩ := source_genus_two_first_return_branch_push_off S hS D B ht i
      have hrawEssential := source_nonseparating_curve_essential S (B.boundary i) hnsraw
      have hdEssential : Essential d := (essential_isotopy_invariant hrel).mp hrawEssential
      let dc : EssentialCurve S := ⟨d,hdEssential⟩
      let rawc : EssentialCurve S := ⟨B.boundary i,hrawEssential⟩
      have hdns : Nonseparating d :=
        (nonseparating_isotopy_invariant (a:=rawc) (b:=dc) hrel).mp hnsraw
      let γ : {v : Vertex S // nonseparatingVertex v} :=
        ⟨Quotient.mk (essentialCurveSetoid S) dc,hdns⟩
      have hγc : geometricIntersection γ.val cv ≤ had.1.toFinset.card := by
        rw [geometricIntersection_symm_of_chart γ.val cv]
        apply Nat.sInf_le
        exact ⟨a,dc,ha,rfl,had,rfl⟩
      have hbudget := (source_surgery_closing_crossings_budget D B ht i).2
      have hfull : (a.val.image ∩ b.val.image).ncard = n := by
        rw [Set.ncard_eq_toFinset_card _ ht.1,hcard]
      have hretain : (source_surgery_retained_crossings B i).ncard+2 ≤ n := by
        simpa only [source_surgery_retained_crossings,hfull] using hbudget
      have hdesc : geometricIntersection γ.val cv < n := hγc.trans_lt (by omega)
      exact ih _ hdesc γ rfl
  obtain ⟨b0,hb0⟩ := source_genus_two_nonseparating_curve_exists S hS
  let β0 : {v : Vertex S // nonseparatingVertex v} :=
    ⟨Quotient.mk (essentialCurveSetoid S) b0,hb0⟩
  obtain ⟨γ,hzero⟩ := reach (geometricIntersection β0.val cv) β0 rfl
  obtain ⟨a,d,ha,hd,ht,hmin⟩ := source_geometric_intersection_attained S cv γ.val
  have hdns : Nonseparating d.val := by
    have hn := γ.property
    rw [← hd] at hn
    exact hn
  have hcardzero : ht.1.toFinset.card = 0 := by
    rw [hmin,geometricIntersection_symm_of_chart cv γ.val,hzero]
  have hdis : Disjoint a.val.image d.val.image := by
    rw [Set.disjoint_iff_inter_eq_empty]
    have he : ht.1.toFinset = ∅ := Finset.card_eq_zero.mp hcardzero
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
  have houtEssential : Essential out := (essential_isotopy_invariant hdout).mp d.property
  let outc : EssentialCurve S := ⟨out,houtEssential⟩
  have houtns : Nonseparating out :=
    (nonseparating_isotopy_invariant (a:=d) (b:=outc) hdout).mp hdns
  refine ⟨outc,houtns,?_⟩
  rw [← hH,hOut]
  apply Set.disjoint_left.mpr
  rintro x ⟨y,hy,hyx⟩ ⟨z,hz,hzx⟩
  have heq : y = z := e.injective (by
    rw [he y,he z]
    change H.finalMap y = H.finalMap z
    exact hyx.trans hzx.symm)
  exact Set.disjoint_left.mp hdis hy (heq ▸ hz)
end CurveComplex

namespace CurveComplexGenusTwo.SourceTopology
open CurveComplex
theorem source_genus_two_full_realization_point_joined_nonseparating
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2)
    (x : curveComplexRealization S 1) :
    ∃ y : NonseparatingLocus S, Joined x y.val := by
  classical
  let K := curveComplex S 1
  let point (v : Vertex S) : RealizationPoint K := realizationVertex K v (K.singleton_mem v)
  have hLocus (v : Vertex S) (hv : nonseparatingVertex v) : point v ∈ NonseparatingLocus S := by
    intro w hw
    have hne : w≠v := by
      intro he
      subst w
      exact (separatingVertex_iff_not_nonseparatingVertex S v).mp hw hv
    exact (realizationVertex_weight K v (K.singleton_mem v) w).trans (ite_eq_right hne)
  have hEdge (v w : Vertex S) (hvw : geometricIntersection v w≤1) : Joined (point v) (point w) := by
    have hface : ({v,w} : Finset (Vertex S)) ∈ K.faces := by
      refine ⟨by simp,?_⟩
      intro α hα β hβ hne
      simp only [Finset.mem_insert,Finset.mem_singleton] at hα hβ
      rcases hα with rfl|rfl <;> rcases hβ with rfl|rfl
      · exact (hne rfl).elim
      · exact hvw
      · rw [geometricIntersection_symm_of_chart]
        exact hvw
      · exact (hne rfl).elim
    let p := (finiteSegmentPath {v,w}
      (finiteSimplexVertex {v,w} v (by simp))
      (finiteSimplexVertex {v,w} w (by simp))).map
      (continuous_faceInclusion_local K {v,w} hface)
    have hpv : point v=faceInclusion K {v,w} hface (finiteSimplexVertex {v,w} v (by simp)) := by
      apply RealizationPoint.ext
      funext u
      simp [point,realizationVertex,finiteSimplexVertex_faceInclusion_weight]
    have hpw : point w=faceInclusion K {v,w} hface (finiteSimplexVertex {v,w} w (by simp)) := by
      apply RealizationPoint.ext
      funext u
      simp [point,realizationVertex,finiteSimplexVertex_faceInclusion_weight]
    exact ⟨p.cast hpv hpw⟩
  obtain ⟨v,hv⟩ := exists_mem_openVertexStar K x
  have hAnchor : starVertexPoint K v x hv=point v := by
    apply RealizationPoint.ext
    funext w
    simp [point,realizationVertex,finiteSimplexVertex_faceInclusion_weight,starVertexPoint,starCone]
  have hxv : Joined x (point v) := by
    rw [← hAnchor]
    exact ⟨radialPath K v x hv⟩
  obtain ⟨c,hc⟩ := Quotient.exists_rep v
  by_cases hnc : Nonseparating c.val
  · have hnv : nonseparatingVertex v := by rw [← hc];exact hnc
    exact ⟨⟨point v,hLocus v hnv⟩,hxv⟩
  · obtain ⟨d,hnd,hdisj⟩ := source_genus_two_separating_curve_disjoint_nonseparating S hS c hnc
    let w : Vertex S := Quotient.mk (essentialCurveSetoid S) d
    have hnw : nonseparatingVertex w := hnd
    have hgeo : geometricIntersection v w=0 := by
      rw [← hc]
      exact geometricIntersection_eq_zero_of_disjoint_representatives c d hdisj
    exact ⟨⟨point w,hLocus w hnw⟩,hxv.trans (hEdge v w (by omega))⟩

theorem source_genus_two_full_curve_realization_pathConnected
    (S : Type) [TopologicalSpace S]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] (hS : IsGenus S 2) :
    PathConnectedSpace (curveComplexRealization S 1) := by
  classical
  obtain ⟨c,_hnc⟩ := source_genus_two_nonseparating_curve_exists S hS
  let v : Vertex S := Quotient.mk (essentialCurveSetoid S) c
  refine ⟨⟨realizationVertex (curveComplex S 1) v ((curveComplex S 1).singleton_mem v)⟩,?_⟩
  intro x y
  obtain ⟨u,hxu⟩ := source_genus_two_full_realization_point_joined_nonseparating S hS x
  obtain ⟨w,hyw⟩ := source_genus_two_full_realization_point_joined_nonseparating S hS y
  obtain ⟨p⟩ := source_genus_two_nonseparating_points_joined S hS u w
  have hmiddle : Joined u.val w.val := ⟨p.map continuous_subtype_val⟩
  exact hxu.trans (hmiddle.trans hyw.symm)
end CurveComplexGenusTwo.SourceTopology
