import CurveComplexGenusTwo.Topology.GlobalArcCollar.ActualSurfaceStripGluing
import CurveComplexGenusTwo.Topology.Orientation.BandSignScaffold
import CurveComplexGenusTwo.Topology.SurfaceRecognition.ClosedCoverHomeomorph
import CurveComplexGenusTwo.Topology.BandGlobalGluing.ParametrizedCrosscutScaffold
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.Compact
import Mathlib.Order.CompleteLatticeIntervals
import CurveComplexGenusTwo.Topology.BandGlobalGluing.ActualWholeWhiskerHalfCollarScaffold
import CurveComplexGenusTwo.Topology.BandGlobalGluing.OrderedBandSubdivision
import CurveComplexGenusTwo.Topology.BandGlobalGluing.FullSquareExtensionHeader
import CurveComplexGenusTwo.Topology.BandGlobalGluing.EndPortNeighborhoods
import CurveComplexGenusTwo.Topology.BandGlobalGluing.SquareIntersection
set_option maxHeartbeats 12000000
open Set Topology unitInterval
namespace CurveComplex
open Schoenflies
-- Actual D-only package; one full source band producer, applied twice after actual base swap.
private theorem outsideBandsPackaging_3581_order (height : I → ℝ) (hm : StrictMono height) (A : I ≃ₜ I)
    (hA : ∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) :
    StrictMono A ∧ A 0=0 ∧ A 1=1 := by
  have hd : 0<height 1-height 0 := sub_pos.mpr (hm (show (0:I)<1 by norm_num))
  refine ⟨?_,?_,?_⟩
  · intro t u htu
    apply hm.lt_iff_lt.mp
    rw [hA,hA]
    exact add_lt_add_right (mul_lt_mul_of_pos_left (show (t:ℝ)<(u:ℝ) from htu) hd) _
  · apply hm.injective
    simpa using hA 0
  · apply hm.injective
    have hh := hA 1
    simpa using hh

private theorem outsideBandsPackaging_4667_axis {S : Type} [TopologicalSpace S] {x y : S}
    (p : Path x y) (G : I × BandWidth → S) (hG : IsEmbedding G)
    (M : I) (hM : 0<M)
    (hGc : ∀ t : I,G (t,⟨0,by norm_num⟩)=p.extend ((M:ℝ)*t))
    (hGmeet : Set.range G ∩ Set.range p=p '' Icc 0 M) :
    ∀ z,G z∈Set.range p ↔ (z.2:ℝ)=0 := by
  intro z
  constructor
  · intro hz
    have hm : G z∈p '' Icc 0 M := hGmeet ▸ ⟨Set.mem_range_self z,hz⟩
    obtain ⟨t,ht,he⟩ := hm
    let u : I := ⟨(t:ℝ)/(M:ℝ),⟨div_nonneg t.property.1 (show 0≤(M:ℝ) from hM.le),
      (div_le_one (show 0<(M:ℝ) from hM)).mpr ht.2⟩⟩
    have hu : (M:ℝ)*(u:ℝ)=(t:ℝ) := by dsimp [u]; field_simp [ne_of_gt (show 0<(M:ℝ) from hM)]
    have hGsame : G (u,⟨0,by norm_num⟩)=G z := by
      rw [hGc,hu,Path.extend_extends']
      exact he
    have hh : (0:ℝ)=(z.2:ℝ) := congrArg (fun q : I × BandWidth => (q.2:ℝ)) (hG.injective hGsame)
    exact hh.symm
  · intro hz
    have hw : z.2=⟨0,by norm_num⟩ := Subtype.ext hz
    rw [show G z=G (z.1,⟨0,by norm_num⟩) by rw [←hw],hGc]
    exact p.extend_range ▸ Set.mem_range_self _

private theorem outsideBandsPackaging_2356_recognize (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1=0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∀ z, B z 1 = 0 ↔ z.val 1 = 0 := by
  intro z
  constructor
  · intro hz
    have hm : B z ∈ (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ :=
      hmeet ▸ ⟨Set.mem_range_self z,hz⟩
    obtain ⟨t,_,ht⟩ := hm
    have he : B z = B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := ht.symm.trans (hc t).symm
    have hh := congrArg (fun z : ↥(Plane.closedSquare 0 1) => z.val 1) (hB.injective he)
    exact hh
  · intro hz
    have hzQ : max |z.val 0| |z.val 1| ≤ 1 := by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
    let t : Icc (-1 : ℝ) 1 := ⟨z.val 0,abs_le.mp ((le_max_left _ _).trans hzQ)⟩
    have he : z = ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact hz
    rw [he,hc]
    rfl

private theorem outsideBandsPackaging_2127_reparam (h : I → ℝ) (hc : Continuous h) (hm : StrictMono h) :
  ∃ A : I ≃ₜ I, ∀ t : I, h (A t)=h 0+(h 1-h 0)*(t:ℝ) := by
  have hd : 0<h 1-h 0 := sub_pos.mpr (hm (by norm_num : (0:I)<1))
  let n : I → I := fun t => ⟨(h t-h 0)/(h 1-h 0),by
    constructor
    · exact div_nonneg (sub_nonneg.mpr (hm.monotone (show (0:I)≤t from t.property.1))) hd.le
    · apply (div_le_one hd).mpr
      exact sub_le_sub_right (hm.monotone (show t≤(1:I) from t.property.2)) _⟩
  have hnc : Continuous n := by dsimp [n]; fun_prop
  have hnmono : StrictMono n := by
    intro t s hts
    change (h t-h 0)/(h 1-h 0)<(h s-h 0)/(h 1-h 0)
    exact (div_lt_div_iff_of_pos_right hd).mpr (sub_lt_sub_right (hm hts) _)
  have hn0 : n 0=0 := by apply Subtype.ext; simp [n]
  have hn1 : n 1=1 := by apply Subtype.ext; simp [n,hd.ne']
  have hnrange : Set.range n=univ := by
    have hh := hnc.image_Icc_of_strictMono hnmono (a:=(0:I)) (b:=(1:I))
    simpa only [←unitInterval.univ_eq_Icc,Set.image_univ,hn0,hn1] using hh
  let J := ((hnc.isClosedEmbedding hnmono.injective).isEmbedding).toHomeomorph
  let K : I ≃ₜ I := J.trans ((Homeomorph.setCongr hnrange).trans (Homeomorph.Set.univ I))
  refine ⟨K.symm,?_⟩
  intro t
  have hh := K.apply_symm_apply t
  have hh' := congrArg (fun z : I => (z:ℝ)) hh
  change (h (K.symm t)-h 0)/(h 1-h 0)=(t:ℝ) at hh'
  have hx := (div_eq_iff hd.ne').mp hh'
  nlinarith


private theorem outsideBandsPackaging_1949_direction {S : Type} [TopologicalSpace S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (γ : I → I) (hγ : StrictAnti γ)
    (hγaxis : ∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
      constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y))
    (M : I) (hM : 0 < M) (r : ℝ) (hr : 0 < r ∧ r < 1/4)
    (height : BandWidth → ℝ) (hb : ∀ t,0 < height t ∧ height t ≤ 1)
    (hcenter : ∀ t : BandWidth,D.ends 0
      (⟨0,by norm_num⟩,⟨height t,by constructor <;> linarith [(hb t).1,(hb t).2]⟩)=
        D.firstArc.extend ((M:ℝ)*(1-2*r+r*(t:ℝ)))) :
    StrictAnti height := by
  have heq (t : BandWidth) :
      (γ ⟨height t,⟨(hb t).1.le,(hb t).2⟩⟩:ℝ)=
        (M:ℝ)*(1-2*r+r*(t:ℝ)) := by
    as_aux_lemma =>
      let v : I := ⟨1-2*r+r*(t:ℝ),by
        constructor <;> nlinarith [t.property.1,t.property.2,hr.1,hr.2]⟩
      let u : I := ⟨(M:ℝ)*v,by
        constructor <;> nlinarith [M.property.1,M.property.2,v.property.1,v.property.2]⟩
      have hh : D.firstArc (γ ⟨height t,⟨(hb t).1.le,(hb t).2⟩⟩)=D.firstArc u := by
        rw [←hγaxis,hcenter]
        exact D.firstArc.extend_extends' u
      exact congrArg Subtype.val (D.firstArc_embedded.injective hh)
  intro t u htu
  by_contra hn
  have hle : height t ≤ height u := le_of_not_gt hn
  have hγle := hγ.antitone (show
    (⟨height t,⟨(hb t).1.le,(hb t).2⟩⟩ : I) ≤
    ⟨height u,⟨(hb u).1.le,(hb u).2⟩⟩ from hle)
  have hγleR : (γ ⟨height u,⟨(hb u).1.le,(hb u).2⟩⟩:ℝ) ≤
    (γ ⟨height t,⟨(hb t).1.le,(hb t).2⟩⟩:ℝ) := hγle
  rw [heq,heq] at hγleR
  have htuR : (t:ℝ)<(u:ℝ) := htu
  have hMR : 0<(M:ℝ) := hM
  have hinner : 1-2*r+r*(t:ℝ) < 1-2*r+r*(u:ℝ) := by
    have hh := mul_lt_mul_of_pos_left htuR hr.1
    linarith
  exact (not_le_of_gt (mul_lt_mul_of_pos_left hinner hMR)) hγleR

private theorem outsideBandsPackaging_2923_patch (A : Set Plane) (hA : IsClosed A) (e : A ≃ₜ A)
    (he : ∀ (x : A), (x : Plane) ∈ frontier A → (e x : Plane) = x) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ x : A,H x = e x) ∧ (∀ x, x ∉ interior A → H x = x) := by
  classical
  obtain ⟨f,g,hfg,hfe⟩ := exists_isHomeoOn_of_homeomorph e
  let C := (interior A)ᶜ
  have hC : IsClosed C := isOpen_interior.isClosed_compl
  have hid : IsHomeoOn id id C C :=
    ⟨fun _ h => h,fun _ h => h,continuous_id.continuousOn,
      continuous_id.continuousOn,fun _ _ => rfl,fun _ _ => rfl⟩
  have hagree : ∀ x ∈ A ∩ C, f x = id x := by
    intro x hx
    rw [hfe x hx.1]
    apply he
    rw [frontier,hA.closure_eq]
    exact hx
  have him : f '' (A ∩ C) = A ∩ C := by
    as_aux_lemma =>
      ext x
      constructor
      · rintro ⟨y,hy,rfl⟩
        rw [hagree y hy]
        exact hy
      · intro hx
        exact ⟨x,hx,hagree x hx⟩
  obtain ⟨F,G,hFG,hF,hFC⟩ := glue_closed_homeoOn hA hC hA hC hfg hid hagree him
  have hcover : A ∪ C = univ := by
    apply Set.eq_univ_of_forall
    intro x
    by_cases hx : x ∈ interior A
    · exact Or.inl (interior_subset hx)
    · exact Or.inr hx
  rw [hcover] at hFG
  refine ⟨hFG.homeomorphOfUniv,?_,?_⟩
  · intro x
    exact (hF x x.property).trans (hfe x x.property)
  · intro x hx
    exact hFC x hx

private theorem outsideBandsPackaging_4045_separate {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (center span : ℝ) (hspan : 0 < span)
    (hcenter : 0 < center ∧ center < 1)
    (E : ↥(Schoenflies.Plane.closedSquare 0 1) → S)
    (hE : ∀ z, ∃ v : EndRectangle,D.ends 0 v=E z ∧
      (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0))
    (T : I × BandWidth → S) (_hT : IsEmbedding T)
    (hcoords : ∀ z, ∃ v : EndRectangle,D.ends 0 v=T z ∧
      (v.2:ℝ)≤center ∧ ((v.2:ℝ)=center ↔ z.1=0))
    (hT0 : ∀ w,T (0,w)=D.ends 0
      (⟨(w:ℝ)/4,by constructor <;> linarith [w.property.1,w.property.2]⟩,
       ⟨center,by constructor <;> linarith [hcenter.1,hcenter.2]⟩)) :
    ∀ z : ↥(Schoenflies.Plane.closedSquare 0 1),0≤z.val 0 →
      |z.val 1|≤1/2 → (E z∈Set.range T ↔ z.val 0=0) := by
  intro z hz hx
  obtain ⟨v,hv,hvx,hvy⟩ := hE z
  constructor
  · rintro ⟨t,ht⟩
    obtain ⟨u,hu,huc,_⟩ := hcoords t
    have he := (D.ends_embedded 0).injective (hu.trans (ht.trans hv.symm))
    have heh := congrArg (fun p : EndRectangle => (p.2:ℝ)) he
    change (u.2:ℝ)=(v.2:ℝ) at heh
    have hh : span*(2*z.val 0) ≤ 0 := by linarith
    exact le_antisymm (by nlinarith [hspan]) hz
  · intro he0
    let w : BandWidth := ⟨2*z.val 1,by
      have hxx := abs_le.mp hx
      constructor <;> linarith⟩
    refine ⟨(0,w),?_⟩
    rw [hT0]
    rw [←hv]
    congr 1
    apply Prod.ext <;> apply Subtype.ext
    · change (2*z.val 1)/4=(v.1:ℝ)
      linarith
    · change center=(v.2:ℝ)
      rw [he0] at hvy
      simpa using hvy.symm

private theorem outsideBandsPackaging_2390_side (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (haxis : ∀ z, B z 1=0 ↔ z.val 1=0) :
    (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∨
    (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) := by
  let A : Set Plane := Plane.closedSquare 0 1 ∩ {z | 0<z 1}
  have hconv : Convex ℝ A := by
    as_aux_lemma =>
      intro x hx y hy a b ha hb hab
      refine ⟨(Plane.convex_closedSquare 0 1) hx.1 hy.1 ha hb hab,?_⟩
      change 0<a*x 1+b*y 1
      by_cases haz : a=0
      · have hb1 : b=1 := by linarith
        simpa [haz,hb1] using hy.2
      · have hap : 0<a := lt_of_le_of_ne ha (Ne.symm haz)
        exact add_pos_of_pos_of_nonneg (mul_pos hap hx.2) (mul_nonneg hb hy.2.le)
  let f : A → Plane := fun z => B ⟨z, z.property.1⟩
  have hfc : Continuous f := hB.continuous.comp (continuous_subtype_val.subtype_mk _)
  have hpreA : IsPreconnected (univ : Set A) := by
    have hconn : PreconnectedSpace A := (isPreconnected_iff_preconnectedSpace).mp hconv.isPreconnected
    letI := hconn
    exact isPreconnected_univ
  have hpre : IsPreconnected (Set.range f) := by
    simpa only [Set.image_univ] using hpreA.image f hfc.continuousOn
  have hcover : Set.range f ⊆ {z : Plane | 0<z 1} ∪ {z : Plane | z 1<0} := by
    rintro z ⟨t,rfl⟩
    have hz : f t 1 ≠ 0 := by
      intro hh
      have h0 := (haxis ⟨t,t.property.1⟩).mp hh
      exact ne_of_gt t.property.2 h0
    exact lt_or_gt_of_ne hz.symm
  have hopenpos : IsOpen {z : Plane | 0<z 1} := isOpen_lt continuous_const (by fun_prop)
  have hopenneg : IsOpen {z : Plane | z 1<0} := isOpen_lt (by fun_prop) continuous_const
  have hdis : Disjoint {z : Plane | 0<z 1} {z : Plane | z 1<0} :=
    Set.disjoint_left.mpr (fun z hz0 hz1 => (lt_asymm (show 0<z 1 from hz0) (show z 1<0 from hz1)))
  rcases hpre.subset_or_subset hopenpos hopenneg hdis hcover with hp | hn
  · left
    intro z hz
    exact hp ⟨⟨z,⟨z.property,hz⟩⟩,rfl⟩
  · right
    intro z hz
    exact hn ⟨⟨z,⟨z.property,hz⟩⟩,rfl⟩

private theorem outsideBandsPackaging_2655_normalize (R : ℝ) (hR : 0 < R) :
    ∃ N : Plane ≃ₜ Plane,
      (∀ z,N z=Plane.mk (z 0/R) (2*z 1/R-1)) ∧
      (∀ z,N z ∈ Plane.openSquare 0 1 ↔ |z 0|<R ∧ 0<z 1 ∧ z 1<R) := by
  let N : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0/R) (2*z 1/R-1)
    invFun := fun z => Plane.mk (R*z 0) (R*(z 1+1)/2)
    left_inv := by
      intro z
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [Plane.mk] <;> field_simp <;> ring
    right_inv := by
      intro z
      apply PiLp.ext
      intro i
      fin_cases i <;> simp [Plane.mk] <;> field_simp <;> ring
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  refine ⟨N,fun z => rfl,?_⟩
  intro z
  rw [mem_openSquare_zero_one]
  change max |z 0/R| |2*z 1/R-1|<1 ↔ _
  rw [max_lt_iff,abs_div,abs_of_pos hR,div_lt_one hR]
  simp only [abs_lt]
  constructor
  · rintro ⟨hx,hy0,hy1⟩
    refine ⟨hx,?_,?_⟩
    · have hh : 0 < 2*z 1/R := by linarith
      have hmul := (div_pos_iff.mp hh)
      rcases hmul with hh | hh
      · linarith [hh.1]
      · linarith [hh.2]
    · have hh : 2*z 1/R < 2 := by linarith
      have hv := (div_lt_iff₀ hR).mp hh
      linarith
  · rintro ⟨hx,hz0,hzR⟩
    refine ⟨hx,?_,?_⟩
    · have hh : 0 < 2*z 1/R := div_pos (by linarith) hR
      linarith
    · have hh : 2*z 1/R < 2 := (div_lt_iff₀ hR).mpr (by linarith)
      linarith

private theorem outsideBandsPackaging_4746_normalize {S : Type} [TopologicalSpace S] [T2Space S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (E : I × BandWidth → S) (hE : IsEmbedding E)
    (hcenterrange : Set.range (fun t : I => E (t,⟨0,by norm_num⟩)) = Set.range p)
    (h0 : E (0,⟨0,by norm_num⟩)=p 0)
    (h1 : E (1,⟨0,by norm_num⟩)=p 1) :
    ∃ A : I ≃ₜ I, A 0=0 ∧ A 1=1 ∧
    ∃ F : I × BandWidth → S, IsEmbedding F ∧
      (∀ t : I,F (t,⟨0,by norm_num⟩)=p t) ∧
      (∀ w,F (0,w)=E (0,w)) ∧ (∀ w,F (1,w)=E (1,w)) ∧
      Set.range F=Set.range E ∧ ∀ z,F z=E (A z.1,z.2) := by
  let f : I → S := fun t => E (t,⟨0,by norm_num⟩)
  have hfc : Continuous f := hE.continuous.comp (continuous_id.prodMk continuous_const)
  have hfi : Function.Injective f := by
    intro t u he
    exact congrArg Prod.fst (hE.injective he)
  have hf : IsEmbedding f := (hfc.isClosedEmbedding hfi).isEmbedding
  let J := hf.toHomeomorph
  let K := hp.toHomeomorph
  let A := K.trans ((Homeomorph.setCongr hcenterrange.symm).trans J.symm)
  have hA (t : I) : E (A t,⟨0,by norm_num⟩)=p t := by
    have hh := congrArg Subtype.val (J.apply_symm_apply
      ((Homeomorph.setCongr hcenterrange.symm) (K t)))
    exact hh
  have hA0 : A 0=0 := by
    exact congrArg Prod.fst (hE.injective ((hA 0).trans h0.symm))
  have hA1 : A 1=1 := by
    exact congrArg Prod.fst (hE.injective ((hA 1).trans h1.symm))
  let F : I × BandWidth → S := fun z => E (A z.1,z.2)
  have hFc : Continuous F := hE.continuous.comp
    ((A.continuous.comp continuous_fst).prodMk continuous_snd)
  have hFi : Function.Injective F := by
    as_aux_lemma =>
      intro z w he
      have hh := hE.injective he
      apply Prod.ext
      · exact A.injective (congrArg Prod.fst hh)
      · change z.2=w.2
        have hh2 : z.2 = w.2 := Prod.mk.inj hh |>.2
        exact hh2
  refine ⟨A,hA0,hA1,F,(hFc.isClosedEmbedding hFi).isEmbedding,hA,?_,?_,?_,fun _ => rfl⟩
  · intro w; change E (A 0,w)=_; rw [hA0]
  · intro w; change E (A 1,w)=_; rw [hA1]
  · apply Set.Subset.antisymm
    · rintro x ⟨z,rfl⟩; exact Set.mem_range_self _
    · rintro x ⟨z,rfl⟩
      refine ⟨(A.symm z.1,z.2),?_⟩
      change E (A (A.symm z.1),z.2)=E z
      rw [A.apply_symm_apply]

private theorem outsideBandsPackaging_4370_core {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (G R : I × BandWidth → S) (M τ cut : I)
    (hcut : 0<cut ∧ cut<1) (hcutparam : (cut:ℝ)=(M:ℝ)*τ)
    (hGc : ∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t))
    (hRc : ∀ t : I,R (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t))
    (hRaxis : ∀ z,R z∈Set.range D.firstArc ↔ (z.2:ℝ)=0)
    (hRsource : Set.range R ∩ Set.range D.square=Set.range
      (fun w => D.square (squarePort D.radius D.radius_pos 0 w)))
    (hG0 : ∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) :
    (∀ t : I,t<1 → G
      (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
       ⟨0,by norm_num⟩)∉Set.range R) ∧
    (∀ w,G (0,w)∉Set.range R) := by
  constructor
  · intro t ht
    let v : I := ⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩
    intro hz
    obtain ⟨z,hz⟩ := hz
    have hvp : G (v,⟨0,by norm_num⟩)∈Set.range D.firstArc := by
      rw [hGc]
      exact D.firstArc.extend_range ▸ Set.mem_range_self _
    have hz0 : z.2=⟨0,by norm_num⟩ := Subtype.ext ((hRaxis z).mp (hz.symm ▸ hvp))
    have hh := hz
    rw [show R z=R (z.1,⟨0,by norm_num⟩) by rw [←hz0],hRc,hGc] at hh
    let u : I := ⟨(cut:ℝ)+(1-(cut:ℝ))*z.1,by
      constructor <;> nlinarith [cut.property.1,cut.property.2,z.1.property.1,z.1.property.2]⟩
    let w : I := ⟨(M:ℝ)*v,by constructor <;> nlinarith [M.property.1,M.property.2,v.property.1,v.property.2]⟩
    have he : D.firstArc u=D.firstArc w := by
      change D.firstArc.extend (u:ℝ)=D.firstArc.extend (w:ℝ) at hh
      simpa only [Path.extend_extends'] using hh
    have heR := congrArg Subtype.val (D.firstArc_embedded.injective he)
    change (cut:ℝ)+(1-(cut:ℝ))*z.1=(M:ℝ)*((τ:ℝ)*t) at heR
    have hprod : (M:ℝ)*((τ:ℝ)*t)=(cut:ℝ)*t := by rw [←mul_assoc,←hcutparam]
    rw [hprod] at heR
    have hleft : (cut:ℝ)≤(cut:ℝ)+(1-(cut:ℝ))*z.1 := by nlinarith [z.1.property.1,cut.property.2]
    have hright : (cut:ℝ)*t<(cut:ℝ) := by
      have hh := mul_lt_mul_of_pos_left (show (t:ℝ)<1 from ht) (show 0<(cut:ℝ) from hcut.1)
      simpa using hh
    linarith
  · intro w hz
    have hQ : G (0,w)∈Set.range D.square := by rw [hG0]; exact Set.mem_range_self _
    have hh : G (0,w)∈Set.range (fun t => D.square (squarePort D.radius D.radius_pos 0 t)) :=
      hRsource ▸ ⟨hz,hQ⟩
    obtain ⟨u,hu⟩ := hh
    have h0 : G (0,w)∈Set.range (D.ends 0) :=
      ⟨(u,⟨0,by norm_num⟩),(D.ends_seam 0 u).trans hu⟩
    have h2 : G (0,w)∈Set.range (D.ends 2) :=
      ⟨(w,⟨0,by norm_num⟩),(D.ends_seam 2 w).trans (hG0 w).symm⟩
    exact Set.disjoint_left.mp (D.ends_disjoint (show (0:Fin 4)≠2 by decide)) h0 h2

private theorem outsideBandsPackaging_4084_seam {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (G : I × BandWidth → S) (r δ width : ℝ)
    (hr : 0 < r ∧ r < 1/4) (hδ : 0 < δ ∧ δ ≤ 1) (hw : 0 < width ∧ width ≤ 1)
    (C : EndRectangle → S)
    (hC : ∀ z,C z=G
      (⟨1-2*r+r*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
       ⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩))
    (q : I → BandWidth) (A : I ≃ₜ I) (F : S ≃ₜ S)
    (flip : Bool) (center span : ℝ)
    (hnative : ∀ z : ↥(Plane.closedSquare 0 1),∃ t : I,∃ w : BandWidth,∃ v : EndRectangle,
      (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
      (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
      (v.2:ℝ)=center+span*z.val 0 ∧ F (D.ends 0 v)=C (q (A t),w))
    (T : I × BandWidth → S)
    (hc : 0 < center ∧ center < 1)
    (hT0 : ∀ w,T (0,w)=D.ends 0
      (⟨(w:ℝ)/4,by constructor <;> linarith [w.property.1,w.property.2]⟩,
       ⟨center,⟨by linarith [hc.1],hc.2.le⟩⟩)) :
    ∀ w : BandWidth,F (T (0,flipBandWidth flip w))=
      G (⟨1-2*r+r*(q (A ⟨1/2,by norm_num⟩):ℝ),by
           constructor <;> nlinarith [(q (A ⟨1/2,by norm_num⟩)).property.1,
             (q (A ⟨1/2,by norm_num⟩)).property.2,hr.1,hr.2]⟩,
         ⟨δ*width*(w:ℝ),by
           have hs : 0<δ*width ∧ δ*width≤1 :=
             ⟨mul_pos hδ.1 hw.1,(mul_le_mul_of_nonneg_left hw.2 hδ.1.le).trans (by simpa using hδ.2)⟩
           constructor <;> nlinarith [w.property.1,w.property.2,hs.1,hs.2]⟩) := by
  intro w
  let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk 0 w,by
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using
      max_le (by norm_num : |(0:ℝ)|≤1) (abs_le.mpr w.property)⟩
  obtain ⟨t,u,v,ht,hu,hvx,hvy,hF⟩ := hnative z
  have ht' : t=⟨1/2,by norm_num⟩ := Subtype.ext (by simpa [z,Plane.mk] using ht)
  have hux : (u:ℝ)=width*(w:ℝ) := by simpa [z,Plane.mk] using hu
  have hvy' : (v.2:ℝ)=center := by simpa [z,Plane.mk] using hvy
  have hvx' : (v.1:ℝ)=(flipBandWidth flip w:ℝ)/4 := by
    cases flip <;> simpa [z,Plane.mk,flipBandWidth] using hvx
  rw [hT0]
  have hv : (⟨(flipBandWidth flip w:ℝ)/4,by
      constructor <;> linarith [(flipBandWidth flip w).property.1,(flipBandWidth flip w).property.2]⟩,
      ⟨center,⟨by linarith [hc.1],hc.2.le⟩⟩)=v := by
    apply Prod.ext <;> apply Subtype.ext
    · exact hvx'.symm
    · exact hvy'.symm
  rw [hv,hF,ht',hC]
  congr 1
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    change δ*(u:ℝ)=δ*width*(w:ℝ)
    rw [hux]
    ring

private theorem outsideBandsPackaging_1431_atlas {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (m M : I) (hmM : m ≤ M) (hM1 : M < 1)
    (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m M ⊆ U) :
    ∃ τ : ℕ → I, τ 0 = m ∧ Monotone τ ∧
      (∃ N, ∀ j ≥ N, τ j = M) ∧
      ∀ j, ∃ (e : OpenPartialHomeomorph S Plane) (n : I),
        τ (j+1) < n ∧ p '' Icc (τ j) n ⊆ e.source ∩ U := by
  have margin (V : Set I) (hV : IsOpen V) (m M : I)
      (hmM : m ≤ M) (hM1 : M < 1) (hsub : Icc m M ⊆ V) :
      ∃ n : I, M < n ∧ Icc m n ⊆ V := by
    as_aux_lemma =>
      have hMV : M ∈ V := hsub ⟨hmM,le_rfl⟩
      obtain ⟨e,he,heV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hMV)
      let d : ℝ := min (e/2) ((1-(M:ℝ))/2)
      have hd : 0 < d := by dsimp [d]; exact lt_min (by linarith) (by change 0 < (1-(M:ℝ))/2; have hh : (M:ℝ)<1 := hM1; linarith)
      have hde : d < e := by have hh := min_le_left (e/2) ((1-(M:ℝ))/2); dsimp [d]; linarith
      have hd1 : (M:ℝ)+d ≤ 1 := by
        have hh := min_le_right (e/2) ((1-(M:ℝ))/2)
        have hm : (M:ℝ)<1 := hM1
        dsimp [d]; linarith
      let n : I := ⟨(M:ℝ)+d,⟨by linarith [M.property.1],hd1⟩⟩
      refine ⟨n,?_,?_⟩
      · change (M:ℝ) < (M:ℝ)+d; linarith
      · intro t ht
        by_cases htM : t ≤ M
        · exact hsub ⟨ht.1,htM⟩
        · apply heV
          have hMt : (M:ℝ) < t := lt_of_not_ge htM
          have htn : (t:ℝ) ≤ (M:ℝ)+d := ht.2
          change dist (t:ℝ) (M:ℝ) < e
          rw [Real.dist_eq,abs_of_nonneg (by linarith)]
          linarith
  let A := Icc (m : ℝ) (M : ℝ)
  let emb : A → I := fun t => ⟨t,⟨le_trans m.property.1 t.property.1,le_trans t.property.2 M.property.2⟩⟩
  have hemb : Continuous emb := by dsimp [emb]; fun_prop
  let c : S → Set A := fun s => (p ∘ emb) ⁻¹' ((chartAt Plane s).source ∩ U)
  have hc : ∀ s, IsOpen (c s) := fun s => ((chartAt Plane s).open_source.inter hU).preimage (p.continuous.comp hemb)
  have hcover : (univ : Set A) ⊆ ⋃ s, c s := by
    intro t _
    exact mem_iUnion.mpr ⟨p (emb t),mem_chart_source Plane (p (emb t)),hpU ⟨emb t, t.property, rfl⟩⟩
  obtain ⟨seq,hseq0,hseqmono,⟨N,hseqend⟩,hseqsub⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc (show (m : ℝ) ≤ M from hmM) hc hcover
  let τ : ℕ → I := fun j => emb (seq j)
  have hτ0 : τ 0 = m := by apply Subtype.ext; exact hseq0
  have hτmono : Monotone τ := by intro i j hij; exact hseqmono hij
  refine ⟨τ,hτ0,hτmono,⟨N,?_⟩,?_⟩
  · intro j hj; apply Subtype.ext; exact hseqend j hj
  · intro j
    obtain ⟨s,hs⟩ := hseqsub j
    let e := chartAt Plane s
    let V := p ⁻¹' (e.source ∩ U)
    have hV : IsOpen V := (e.open_source.inter hU).preimage p.continuous
    have hs' : Icc (τ j) (τ (j+1)) ⊆ V := by
      intro t ht
      let t' : A := ⟨t,⟨le_trans (seq j).property.1 ht.1,le_trans ht.2 (seq (j+1)).property.2⟩⟩
      have ht' : t' ∈ Icc (seq j) (seq (j+1)) := ht
      have hh := hs ht'
      exact hh
    have hjM : τ (j+1) < 1 := lt_of_le_of_lt (seq (j+1)).property.2 hM1
    obtain ⟨n,hn,hnV⟩ := margin V hV (τ j) (τ (j+1)) (hτmono (Nat.le_succ j)) hjM hs'
    exact ⟨e,n,hn,Set.image_subset_iff.mpr hnV⟩

private theorem outsideBandsPackaging_1821_window (height : BandWidth → ℝ) (hh : Continuous height)
    (hm : StrictMono height ∨ StrictAnti height)
    (hb : ∀ t, 0 < height t ∧ height t ≤ 1) :
    ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
      ∀ x : ℝ, |x| ≤ 2 →
        0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
        (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1 := by
  let zero : BandWidth := ⟨0,by norm_num⟩
  let h := height zero
  have hh0 : 0 < h := (hb zero).1
  have hh1 : h < 1 := by
    rcases hm with hm | hm
    · exact (hm (show zero < (⟨1,by norm_num⟩ : BandWidth) by norm_num [zero])).trans_le (hb _).2
    · exact (hm (show (⟨-1,by norm_num⟩ : BandWidth) < zero by norm_num [zero])).trans_le (hb _).2
  let m := min h (1-h)
  have hm0 : 0 < m := lt_min hh0 (by linarith)
  have hmh : m ≤ h := min_le_left _ _
  have hm1 : m ≤ 1-h := min_le_right _ _
  have hn : height ⁻¹' Ioo (h-m/8) (h+m/8) ∈ 𝓝 zero :=
    hh.continuousAt.preimage_mem_nhds
      (isOpen_Ioo.mem_nhds ⟨by linarith,by linarith⟩)
  obtain ⟨d,hd,hdV⟩ := Metric.mem_nhds_iff.mp hn
  let s := min (d/2) (1/2:ℝ)
  have hs0 : 0 < s := lt_min (half_pos hd) (by norm_num)
  have hs1 : s ≤ 1/2 := min_le_right _ _
  have hsd : s < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  let lo : BandWidth := ⟨-s,by constructor <;> linarith⟩
  let hi : BandWidth := ⟨s,by constructor <;> linarith⟩
  have hlo : height lo ∈ Ioo (h-m/8) (h+m/8) := by
    apply hdV
    change dist lo zero < d
    rw [Subtype.dist_eq,Real.dist_eq]
    simpa [lo,zero,abs_of_pos hs0] using hsd
  have hhi : height hi ∈ Ioo (h-m/8) (h+m/8) := by
    apply hdV
    change dist hi zero < d
    rw [Subtype.dist_eq,Real.dist_eq]
    simpa [hi,zero,abs_of_pos hs0] using hsd
  refine ⟨s,⟨hs0,hs1⟩,?_⟩
  intro x hx
  change 0 < (height lo+height hi)/2+(height hi-height lo)/2*x ∧
    (height lo+height hi)/2+(height hi-height lo)/2*x < 1
  have hxlo := (abs_le.mp hx).1
  have hxhi := (abs_le.mp hx).2
  have hdifflo : -m/4 < height hi-height lo := by linarith [hlo.1,hlo.2,hhi.1,hhi.2]
  have hdiffhi : height hi-height lo < m/4 := by linarith [hlo.1,hlo.2,hhi.1,hhi.2]
  have hprodlo : -m/2 < (height hi-height lo)*x := by
    by_cases hx0 : 0 ≤ x
    · nlinarith
    · nlinarith
  have hprodhi : (height hi-height lo)*x < m/2 := by
    by_cases hx0 : 0 ≤ x
    · nlinarith
    · nlinarith
  constructor <;> nlinarith [hlo.1,hlo.2,hhi.1,hhi.2]

private theorem outsideBandsPackaging_1882_axisParameter {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ γ : I → I, Continuous γ ∧ StrictAnti γ ∧ γ 0=1 ∧ 0<γ 1 ∧
      (∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
        constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y)) ∧
      ∀ y : I,D.firstArc '' Icc (γ y) 1 ⊆ Set.range (D.ends 0) := by
  let axis : I → EndRectangle := fun y =>
    (⟨0,by norm_num⟩,⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩)
  have haxisC : Continuous axis := by dsimp [axis]; fun_prop
  have hmem (y : I) : D.ends 0 (axis y) ∈ Set.range D.firstArc := by
    as_aux_lemma =>
      by_cases hy : y=0
      · subst y
        have he : D.ends 0 (axis 0)=D.firstArc 1 := by
          change D.ends 0 (⟨0,by norm_num⟩,⟨0,by norm_num⟩)=D.firstArc 1
          rw [D.ends_seam,D.firstArc.target]
        exact ⟨1,he.symm⟩
      · rw [D.firstArc_range]
        refine ⟨(D.ends_axes 0 (axis y)).1.mpr ⟨Or.inl rfl,rfl⟩,?_⟩
        have hy0 : 0<(y:ℝ) := lt_of_le_of_ne y.property.1 (by
          intro he; apply hy; exact Subtype.ext he.symm)
        intro ho
        rw [D.openSquare_eq] at ho
        obtain ⟨z,hz,hze⟩ := ho
        have hQ : D.ends 0 (axis y) ∈ Set.range D.square := ⟨z,hze⟩
        exact (not_le_of_gt hy0) ((D.ends_square 0 (axis y)).mp hQ)
  let J := D.firstArc_embedded.toHomeomorph
  let u : I → Set.range D.firstArc := fun y => ⟨D.ends 0 (axis y),hmem y⟩
  have huc : Continuous u := ((D.ends_embedded 0).continuous.comp haxisC).subtype_mk _
  let γ : I → I := J.symm ∘ u
  have hγc : Continuous γ := J.symm.continuous.comp huc
  have hγ (y : I) : D.ends 0 (axis y)=D.firstArc (γ y) :=
    (congrArg Subtype.val (J.apply_symm_apply (u y))).symm
  have hγi : Function.Injective γ := by
    intro y z he
    have hh := (D.ends_embedded 0).injective
      ((hγ y).trans ((congrArg D.firstArc he).trans (hγ z).symm))
    apply Subtype.ext
    exact congrArg (fun q : EndRectangle => (q.2:ℝ)) hh
  have hγ0 : γ 0=1 := by
    apply D.firstArc_embedded.injective
    rw [←hγ,D.firstArc.target]
    exact D.ends_seam 0 ⟨0,by norm_num⟩
  have hγanti : StrictAnti γ := by
    rcases hγc.strictMono_of_inj_boundedOrder' hγi with hm | ha
    · have hh := hm (show (0:I)<1 by norm_num)
      rw [hγ0] at hh
      exact False.elim ((not_lt_of_ge (γ 1).property.2) hh)
    · exact ha
  have hγ1 : 0<γ 1 := by
    as_aux_lemma =>
      apply lt_of_le_of_ne (γ 1).property.1
      intro he
      have hzero : γ 1=0 := Subtype.ext he.symm
      have hQ0 : D.firstArc 0 ∈ Set.range (D.ends 0) := by
        exact ⟨axis 1,(hγ 1).trans (congrArg D.firstArc hzero)⟩
      have hQ2 : D.firstArc 0 ∈ Set.range (D.ends 2) := by
        refine ⟨(⟨0,by norm_num⟩,⟨0,by norm_num⟩),?_⟩
        rw [D.ends_seam,D.firstArc.source]
      exact Set.disjoint_left.mp (D.ends_disjoint (show (0:Fin 4)≠2 by decide)) hQ0 hQ2
  refine ⟨γ,hγc,hγanti,hγ0,hγ1,hγ,?_⟩
  intro y
  have himage : γ '' Icc (0:I) y = Icc (γ y) 1 := by
    have hh := ContinuousOn.image_Icc_of_antitoneOn
      (show (0:I) ≤ y from y.property.1) hγc.continuousOn (hγanti.antitone.antitoneOn _)
    simpa [hγ0] using hh
  rintro x ⟨t,ht,rfl⟩
  obtain ⟨z,hz,hzt⟩ := (himage.symm ▸ ht)
  exact ⟨axis z,(hγ z).trans (congrArg D.firstArc hzt)⟩

private theorem outsideBandsPackaging_3710_axisParameter {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ γ : I → I, Continuous γ ∧ StrictAnti γ ∧ γ 0=1 ∧ 0<γ 1 ∧
      (∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
        constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y)) ∧
      ∀ y : I,D.firstArc '' Icc (γ y) 1 ⊆ Set.range (D.ends 0) := by
  let axis : I → EndRectangle := fun y =>
    (⟨0,by norm_num⟩,⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩)
  have haxisC : Continuous axis := by dsimp [axis]; fun_prop
  have hmem (y : I) : D.ends 0 (axis y) ∈ Set.range D.firstArc := by
    as_aux_lemma =>
      by_cases hy : y=0
      · subst y
        have he : D.ends 0 (axis 0)=D.firstArc 1 := by
          change D.ends 0 (⟨0,by norm_num⟩,⟨0,by norm_num⟩)=D.firstArc 1
          rw [D.ends_seam,D.firstArc.target]
        exact ⟨1,he.symm⟩
      · rw [D.firstArc_range]
        refine ⟨(D.ends_axes 0 (axis y)).1.mpr ⟨Or.inl rfl,rfl⟩,?_⟩
        have hy0 : 0<(y:ℝ) := lt_of_le_of_ne y.property.1 (by
          intro he; apply hy; exact Subtype.ext he.symm)
        intro ho
        rw [D.openSquare_eq] at ho
        obtain ⟨z,hz,hze⟩ := ho
        have hQ : D.ends 0 (axis y) ∈ Set.range D.square := ⟨z,hze⟩
        exact (not_le_of_gt hy0) ((D.ends_square 0 (axis y)).mp hQ)
  let J := D.firstArc_embedded.toHomeomorph
  let u : I → Set.range D.firstArc := fun y => ⟨D.ends 0 (axis y),hmem y⟩
  have huc : Continuous u := ((D.ends_embedded 0).continuous.comp haxisC).subtype_mk _
  let γ : I → I := J.symm ∘ u
  have hγc : Continuous γ := J.symm.continuous.comp huc
  have hγ (y : I) : D.ends 0 (axis y)=D.firstArc (γ y) :=
    (congrArg Subtype.val (J.apply_symm_apply (u y))).symm
  have hγi : Function.Injective γ := by
    intro y z he
    have hh := (D.ends_embedded 0).injective
      ((hγ y).trans ((congrArg D.firstArc he).trans (hγ z).symm))
    apply Subtype.ext
    exact congrArg (fun q : EndRectangle => (q.2:ℝ)) hh
  have hγ0 : γ 0=1 := by
    apply D.firstArc_embedded.injective
    rw [←hγ,D.firstArc.target]
    exact D.ends_seam 0 ⟨0,by norm_num⟩
  have hγanti : StrictAnti γ := by
    rcases hγc.strictMono_of_inj_boundedOrder' hγi with hm | ha
    · have hh := hm (show (0:I)<1 by norm_num)
      rw [hγ0] at hh
      exact False.elim ((not_lt_of_ge (γ 1).property.2) hh)
    · exact ha
  have hγ1 : 0<γ 1 := by
    as_aux_lemma =>
      apply lt_of_le_of_ne (γ 1).property.1
      intro he
      have hzero : γ 1=0 := Subtype.ext he.symm
      have hQ0 : D.firstArc 0 ∈ Set.range (D.ends 0) := by
        exact ⟨axis 1,(hγ 1).trans (congrArg D.firstArc hzero)⟩
      have hQ2 : D.firstArc 0 ∈ Set.range (D.ends 2) := by
        refine ⟨(⟨0,by norm_num⟩,⟨0,by norm_num⟩),?_⟩
        rw [D.ends_seam,D.firstArc.source]
      exact Set.disjoint_left.mp (D.ends_disjoint (show (0:Fin 4)≠2 by decide)) hQ0 hQ2
  refine ⟨γ,hγc,hγanti,hγ0,hγ1,hγ,?_⟩
  intro y
  have himage : γ '' Icc (0:I) y = Icc (γ y) 1 := by
    have hh := ContinuousOn.image_Icc_of_antitoneOn
      (show (0:I) ≤ y from y.property.1) hγc.continuousOn (hγanti.antitone.antitoneOn _)
    simpa [hγ0] using hh
  rintro x ⟨t,ht,rfl⟩
  obtain ⟨z,hz,hzt⟩ := (himage.symm ▸ ht)
  exact ⟨axis z,(hγ z).trans (congrArg D.firstArc hzt)⟩

private theorem outsideBandsPackaging_3488_native {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (C : EndRectangle → S) (c : EndRectangle → Plane)
    (hc : ∀ z, ∃ v : EndRectangle,D.ends 0 v=C z ∧ c z=Plane.mk v.2 v.1)
    (q : I → BandWidth) (P : I × BandWidth → Plane)
    (hP : ∀ z,P z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1))
    (h : I → ℝ) (hd : h 1-h 0 ≠ 0)
    (width : ℝ) (A : I ≃ₜ I) (flip : Bool) (H : Plane ≃ₜ Plane)
    (hH : ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
      (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
      H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
        Plane.mk ((2*(P (A t,w) 0-h 0))/(h 1-h 0)-1) (P (A t,w) 1))
    (E : ↥(Plane.closedSquare 0 1) → S)
    (hE : ∀ z, ∃ v : EndRectangle,D.ends 0 v=E z ∧
      (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*(2*z.val 0))
    (F : S ≃ₜ S)
    (hF : ∀ z : ↥(Plane.closedSquare 0 1), ∃ w : ↥(Plane.closedSquare 0 1),
      w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w) :
    ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth, ∃ v : EndRectangle,
      (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
      (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
      (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*z.val 0 ∧
      F (D.ends 0 v)=C (q (A t),w) := by
  intro z
  have hz : max |z.val 0| |z.val 1| ≤ 1 := by
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
  have hx := (le_max_left _ _).trans hz
  have hy := (le_max_right _ _).trans hz
  let sign := if flip then -(z.val 1) else z.val 1
  have hsign : |sign|≤1 := by dsimp [sign]; split_ifs <;> simpa using hy
  let zin : ↥(Plane.closedSquare 0 1) := ⟨(1/2:ℝ) • Plane.mk (z.val 0) sign,by
    have hhx : |(1/2:ℝ)*z.val 0|≤1 := by rw [abs_mul]; norm_num; linarith
    have hhy : |(1/2:ℝ)*sign|≤1 := by rw [abs_mul]; norm_num; linarith
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hhx hhy⟩
  have hzin : (2:ℝ) • zin.val=Plane.mk (z.val 0) sign := by
    dsimp [zin]
    ext i
    fin_cases i <;> simp [Plane.mk]
  obtain ⟨v,hv,hvx,hvy⟩ := hE zin
  obtain ⟨zout,hzout,hFz⟩ := hF zin
  obtain ⟨vo,hvo,hvox,hvoy⟩ := hE zout
  obtain ⟨t,w,ht,hw,hHz⟩ := hH z
  obtain ⟨vc,hvc,hcc⟩ := hc (q (A t),w)
  rw [hzin] at hzout
  change zout.val=(1/2:ℝ) • H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) at hzout
  rw [hHz] at hzout
  have hout0 := congrArg (fun p : Plane => p 0) hzout
  have hout1 := congrArg (fun p : Plane => p 1) hzout
  change zout.val 0=(1/2:ℝ)*((2*(P (A t,w) 0-h 0))/(h 1-h 0)-1) at hout0
  change zout.val 1=(1/2:ℝ)*(P (A t,w) 1) at hout1
  have hc0 := congrArg (fun p : Plane => p 0) hcc
  have hc1 := congrArg (fun p : Plane => p 1) hcc
  change c (q (A t),w) 0=(vc.2:ℝ) at hc0
  change c (q (A t),w) 1=(vc.1:ℝ) at hc1
  have hp0 : P (A t,w) 0=c (q (A t),w) 0 := by
    simpa [Plane.mk] using congrArg (fun p : Plane => p 0) (hP (A t,w))
  have hp1 : P (A t,w) 1=4*c (q (A t),w) 1 := by
    simpa [Plane.mk] using congrArg (fun p : Plane => p 1) (hP (A t,w))
  rw [hp0,hc0] at hout0
  rw [hp1,hc1] at hout1
  have hxdiv : (2*((vc.2:ℝ)-h 0))/(h 1-h 0)=2*zout.val 0+1 := by linarith
  have hxmul := (div_eq_iff hd).mp hxdiv
  have hvoeq : vo=vc := by
    apply Prod.ext <;> apply Subtype.ext
    · nlinarith only [hvox,hout1]
    · nlinarith only [hvoy,hxmul]
  refine ⟨t,w,v,ht,hw,?_,?_,?_⟩
  · change (v.1:ℝ)=sign/4
    change (v.1:ℝ)=((1/2:ℝ)*sign)/2 at hvx
    linarith
  · change (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*(2*((1/2:ℝ)*z.val 0)) at hvy
    nlinarith only [hvy]
  · rw [hv,hFz,←hvo,hvoeq,hvc]

private theorem outsideBandsPackaging_1735_coordinates {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (C : EndRectangle → S) (hC : IsEmbedding C)
    (hends : Set.range C ⊆ Set.range (D.ends 0))
    (houtside : Disjoint (Set.range C) (Set.range D.square))
    (haxisC : ∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) :
    ∃ c : EndRectangle → Plane, IsEmbedding c ∧
      (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
      (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
      ∃ height : BandWidth → ℝ, Continuous height ∧
        (∀ t, 0 < height t ∧ height t ≤ 1) ∧
        (StrictMono height ∨ StrictAnti height) ∧
        ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0 := by
  let : Fact ((-1:ℝ) ≤ 1) := ⟨by norm_num⟩
  let J := (D.ends_embedded 0).toHomeomorph
  let u : EndRectangle → Set.range (D.ends 0) := fun z =>
    ⟨C z,hends (Set.mem_range_self z)⟩
  have huc : Continuous u := hC.continuous.subtype_mk _
  let g : EndRectangle → EndRectangle := J.symm ∘ u
  have hgc : Continuous g := J.symm.continuous.comp huc
  have hg (z) : D.ends 0 (g z)=C z := congrArg Subtype.val (J.apply_symm_apply (u z))
  have hgi : Function.Injective g := by
    intro z w he
    apply hC.injective
    exact (hg z).symm.trans ((congrArg (D.ends 0) he).trans (hg w))
  let c : EndRectangle → Plane := fun z => Plane.mk (g z).2 (g z).1
  have hcc : Continuous c := by dsimp [c]; fun_prop
  have hci : Function.Injective c := by
    intro z w he
    apply hgi
    apply Prod.ext <;> apply Subtype.ext
    · exact congrArg (fun z : Plane => z 1) he
    · exact congrArg (fun z : Plane => z 0) he
  have haxis (z : EndRectangle) : c z 1 = 0 ↔ (z.2 : ℝ) = 0 := by
    as_aux_lemma =>
      have hcoord : c z 1 = 0 ↔ C z ∈ a.image := by
        have hh := (D.ends_axes 0 (g z)).1
        rw [hg] at hh
        simpa [c] using hh.symm
      rw [hcoord]
      have hnot : C z ∉ D.openSquare := by
        intro ho
        rw [D.openSquare_eq] at ho
        obtain ⟨q,hq,hqe⟩ := ho
        exact Set.disjoint_left.mp houtside (Set.mem_range_self z) ⟨q,hqe⟩
      have hh : C z ∈ a.image ↔ C z ∈ Set.range D.firstArc := by
        rw [D.firstArc_range]
        exact ⟨fun hz => ⟨hz,hnot⟩,fun hz => hz.1⟩
      exact hh.trans (haxisC z)
  let height : BandWidth → ℝ := fun t => c (t,⟨0,by norm_num⟩) 0
  have hheight : Continuous height := by dsimp [height]; fun_prop
  have hcaxis (t : BandWidth) : c (t,⟨0,by norm_num⟩) 1 = 0 := (haxis _).mpr rfl
  have hheighti : Function.Injective height := by
    as_aux_lemma =>
      intro t u he
      have hh : c (t,⟨0,by norm_num⟩)=c (u,⟨0,by norm_num⟩) := by
        apply PiLp.ext
        intro i
        fin_cases i
        · exact he
        · exact (hcaxis t).trans (hcaxis u).symm
      exact congrArg Prod.fst (hci hh)
  have hhb (t : BandWidth) : 0 < height t ∧ height t ≤ 1 := by
    as_aux_lemma =>
      have hpos : 0 < ((g (t,⟨0,by norm_num⟩)).2 : ℝ) := by
        by_contra hn
        have hQ : D.ends 0 (g (t,⟨0,by norm_num⟩)) ∈ Set.range D.square :=
          (D.ends_square 0 _).mpr (le_of_not_gt hn)
        rw [hg] at hQ
        exact Set.disjoint_left.mp houtside (Set.mem_range_self _) hQ
      exact ⟨hpos,(g (t,⟨0,by norm_num⟩)).2.property.2⟩
  refine ⟨c,(hcc.isClosedEmbedding hci).isEmbedding,haxis,
    (fun z => ⟨g z,hg z,rfl⟩),height,hheight,hhb,
    hheight.strictMono_of_inj_boundedOrder' hheighti,?_⟩
  intro t
  apply PiLp.ext
  intro i
  fin_cases i
  · rfl
  · exact hcaxis t

private theorem outsideBandsPackaging_2008_prepare (c : EndRectangle → Plane) (hc : IsEmbedding c)
    (height : BandWidth → ℝ) (hh : Continuous height)
    (ha : StrictAnti height)
    (hc0 : ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
    (haxis : ∀ z,c z 1=0 ↔ (z.2:ℝ)=0)
    (s : ℝ) (hs : 0 < s ∧ s ≤ 1/2)
    (hwindow : ∀ x : ℝ, |x| ≤ 2 →
      0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩+
        height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
        (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩-
          height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
      (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩+
        height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
        (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩-
          height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1) :
    ∃ q : I → BandWidth, Continuous q ∧ Function.Injective q ∧
      (∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ))) ∧
    ∃ C : I × BandWidth → Plane, IsEmbedding C ∧
      (∀ z,C z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)) ∧
    ∃ h : I → ℝ, Continuous h ∧ StrictMono h ∧
      (∀ t,h t=height (q t)) ∧
      (∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (h t) 0) ∧
      (∀ z,C z 1=0 ↔ (z.2:ℝ)=0) ∧
      ∀ x : ℝ, |x| ≤ 2 →
        0 < (h 0+h 1)/2+(h 1-h 0)/2*x ∧
        (h 0+h 1)/2+(h 1-h 0)/2*x < 1 := by
  have finish (q : I → BandWidth) (hqc : Continuous q) (hqi : Function.Injective q)
      (hqform : ∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ)))
      (hmono : StrictMono (height ∘ q))
      (hwin : ∀ x : ℝ, |x| ≤ 2 →
        0 < (height (q 0)+height (q 1))/2+(height (q 1)-height (q 0))/2*x ∧
        (height (q 0)+height (q 1))/2+(height (q 1)-height (q 0))/2*x < 1) :
      ∃ q : I → BandWidth, Continuous q ∧ Function.Injective q ∧
        (∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ))) ∧
      ∃ C : I × BandWidth → Plane, IsEmbedding C ∧
        (∀ z,C z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)) ∧
      ∃ h : I → ℝ, Continuous h ∧ StrictMono h ∧
        (∀ t,h t=height (q t)) ∧
        (∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (h t) 0) ∧
        (∀ z,C z 1=0 ↔ (z.2:ℝ)=0) ∧
        ∀ x : ℝ, |x| ≤ 2 →
          0 < (h 0+h 1)/2+(h 1-h 0)/2*x ∧
          (h 0+h 1)/2+(h 1-h 0)/2*x < 1 := by
    as_aux_lemma =>
      let C : I × BandWidth → Plane := fun z =>
        Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)
      have hCc : Continuous C := by dsimp [C]; fun_prop
      have hCi : Function.Injective C := by
        as_aux_lemma =>
          intro z w he
          have he0 := congrArg (fun v : Plane => v 0) he
          have he1 := congrArg (fun v : Plane => v 1) he
          have hec : c (q z.1,z.2)=c (q w.1,w.2) := by
            as_aux_lemma =>
              apply PiLp.ext
              intro i
              fin_cases i
              · exact he0
              · change c (q z.1,z.2) 1 = c (q w.1,w.2) 1
                change 4*c (q z.1,z.2) 1=4*c (q w.1,w.2) 1 at he1
                linarith
          have hh := hc.injective hec
          apply Prod.ext
          · exact hqi (congrArg Prod.fst hh)
          · exact congrArg (fun p : EndRectangle => p.2) hh
      refine ⟨q,hqc,hqi,hqform,C,(hCc.isClosedEmbedding hCi).isEmbedding,
        (fun _ => rfl),height ∘ q,hh.comp hqc,hmono,(fun _ => rfl),?_,?_,hwin⟩
      · intro t
        dsimp [C]
        rw [hc0]
        simp [Plane.mk]
      · intro z
        change 4*c (q z.1,z.2) 1=0 ↔ (z.2:ℝ)=0
        rw [mul_eq_zero]
        simpa using haxis (q z.1,z.2)
  let q : I → BandWidth := fun t => ⟨s*(1-2*(t:ℝ)),by
    constructor <;> nlinarith [t.property.1,t.property.2,hs.1,hs.2]⟩
  have hqc : Continuous q := by dsimp [q]; fun_prop
  have hqm : StrictAnti q := by intro t u h; change s*(1-2*(u:ℝ))<s*(1-2*(t:ℝ)); have hR : (t:ℝ) < (u:ℝ) := h; nlinarith [hs.1]
  apply finish q hqc hqm.injective (fun _ => rfl) (ha.comp hqm)
  intro x hx
  have hq0 : q 0=⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ := by apply Subtype.ext; norm_num [q]
  have hq1 : q 1=⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ := by apply Subtype.ext; norm_num [q]
  rw [hq0,hq1]
  convert hwindow (-x) (by simpa using hx) using 1 <;> ring_nf

private theorem outsideBandsPackaging_4882_swapBase {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b) :
    ∃ E : OneCrossingBandBase b a,
      (∀ t,E.firstArc t=D.secondArc t) ∧
      (∀ t,E.secondArc t=D.firstArc t) ∧
      (∀ w,E.square (squarePort E.radius E.radius_pos 2 w)=D.square (squarePort D.radius D.radius_pos 3 w)) ∧
      (∀ w,E.square (squarePort E.radius E.radius_pos 0 w)=D.square (squarePort D.radius D.radius_pos 1 w)) ∧
      Set.range E.square=Set.range D.square ∧
      Set.range (E.ends 1) ∪ Set.range (E.ends 3)=Set.range (D.ends 0) ∪ Set.range (D.ends 2) := by
  classical
  let p : Fin 4 → Fin 4 := fun i => match i with | 0=>1 | 1=>0 | 2=>3 | 3=>2
  have hp (i : Fin 4) : p (p i)=i := by fin_cases i <;> rfl
  have hpi : Function.Injective p := by intro i j h; simpa only [hp] using congrArg p h
  let swap : Metric.closedBall ((0,0):ℝ×ℝ) D.radius → Metric.closedBall ((0,0):ℝ×ℝ) D.radius := fun z =>
    ⟨(z.val.2,z.val.1),by
      have hz := z.property
      simp only [Metric.mem_closedBall,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
        Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs] at hz ⊢
      simpa only [max_comm] using hz⟩
  have hswapC : Continuous swap := by dsimp [swap]; fun_prop
  have hswapInv (z) : swap (swap z)=z := by apply Subtype.ext; rfl
  have hswapI : Function.Injective swap := by intro z w h; simpa only [hswapInv] using congrArg swap h
  have hswapE : IsEmbedding swap := (hswapC.isClosedEmbedding hswapI).isEmbedding
  have hport (i : Fin 4) (w : BandWidth) :
      swap (squarePort D.radius D.radius_pos i w)=squarePort D.radius D.radius_pos (p i) w := by
    apply Subtype.ext
    fin_cases i <;> rfl
  let square := D.square ∘ swap
  have hsqRange : Set.range square=Set.range D.square := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩; exact Set.mem_range_self (swap z)
    · rintro ⟨z,rfl⟩
      exact ⟨swap z,congrArg D.square (hswapInv z)⟩
  have hop : D.openSquare=square '' {z | z.val∈Metric.ball ((0,0):ℝ×ℝ) D.radius} := by
    as_aux_lemma =>
      rw [D.openSquare_eq]
      have hball (z) : (swap z).val∈Metric.ball ((0,0):ℝ×ℝ) D.radius ↔ z.val∈Metric.ball ((0,0):ℝ×ℝ) D.radius := by
        simp only [swap,Metric.mem_ball,dist_eq_norm,Prod.norm_def,Prod.fst_sub,Prod.snd_sub,
          Prod.fst_zero,Prod.snd_zero,sub_zero,Real.norm_eq_abs,max_comm]
      ext x
      constructor
      · rintro ⟨z,hz,rfl⟩
        refine ⟨swap z,(hball z).mpr hz,?_⟩
        exact congrArg D.square (hswapInv z)
      · rintro ⟨z,hz,rfl⟩
        exact ⟨swap z,(hball z).mpr hz,rfl⟩
  have hportSq (i : Fin 4) (w : BandWidth) : square (squarePort D.radius D.radius_pos i w)=D.square (squarePort D.radius D.radius_pos (p i) w) := congrArg D.square (hport i w)
  let first := D.secondArc.cast (hportSq 2 ⟨0,by norm_num⟩) (hportSq 0 ⟨0,by norm_num⟩)
  let second := D.firstArc.cast (hportSq 3 ⟨0,by norm_num⟩) (hportSq 1 ⟨0,by norm_num⟩)
  have hfirst : (first : I → S)=D.secondArc := rfl
  have hsecond : (second : I → S)=D.firstArc := rfl
  let E : OneCrossingBandBase b a := {
    radius := D.radius
    radius_pos := D.radius_pos
    square := square
    square_embedded := D.square_embedded.comp hswapE
    openSquare := D.openSquare
    openSquare_open := D.openSquare_open
    openSquare_eq := hop
    firstArc := first
    secondArc := second
    firstArc_embedded := by rw [hfirst]; exact D.secondArc_embedded
    secondArc_embedded := by rw [hsecond]; exact D.firstArc_embedded
    firstArc_range := by rw [hfirst]; exact D.secondArc_range
    secondArc_range := by rw [hsecond]; exact D.firstArc_range
    arcs_disjoint := by rw [hfirst,hsecond]; exact D.arcs_disjoint.symm
    first_axis := fun z => D.second_axis (swap z)
    second_axis := fun z => D.first_axis (swap z)
    ends := fun i => D.ends (p i)
    ends_embedded := fun i => D.ends_embedded (p i)
    ends_disjoint := fun i j hij => D.ends_disjoint (fun he => hij (hpi he))
    ends_square := by intro i z; rw [hsqRange]; exact D.ends_square (p i) z
    ends_seam := by intro i w; rw [hportSq]; exact D.ends_seam (p i) w
    ends_axes := by
      intro i z
      have h := D.ends_axes (p i) z
      fin_cases i <;> simpa [p] using h.symm
  }
  refine ⟨E,?_,?_,?_,?_,hsqRange,?_⟩
  · intro t; rfl
  · intro t; rfl
  · exact hportSq 2
  · exact hportSq 0
  · rfl

private theorem outsideBandsPackaging_4136_germ {S : Type} [TopologicalSpace S] {a b : Curve S}
    (D : OneCrossingBandBase a b)
    (G : I × BandWidth → S) (r δ width : ℝ)
    (hr : 0 < r ∧ r < 1/4) (hδ : 0 < δ ∧ δ ≤ 1) (hw : 0 < width ∧ width ≤ 1)
    (C : EndRectangle → S)
    (hC : ∀ z,C z=G
      (⟨1-2*r+r*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
       ⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩))
    (q : I → BandWidth) (A : I ≃ₜ I) (F : S ≃ₜ S)
    (flip : Bool) (center span : ℝ)
    (hnative : ∀ z : ↥(Plane.closedSquare 0 1),∃ t : I,∃ w : BandWidth,∃ v : EndRectangle,
      (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
      (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
      (v.2:ℝ)=center+span*z.val 0 ∧ F (D.ends 0 v)=C (q (A t),w))
    (E : ↥(Plane.closedSquare 0 1) → S)
    (hE : ∀ z,∃ v : EndRectangle,D.ends 0 v=E z ∧
      (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0))
    (T : I × BandWidth → S)
    (hsep : ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 0 → |z.val 1|≤1/2 →
      (E z∈Set.range T ↔ z.val 0=0))
    (τ c : I) (_hc : 0<c ∧ c<1)
    (u : I → I) (hu : ∀ t : I,c≤t → ⟨1/2,by norm_num⟩≤u t)
    (hu1 : ∀ t : I,c≤t → (u t=⟨1/2,by norm_num⟩ ↔ t=1))
    (hparam : ∀ t : I,c≤t → (τ:ℝ)*t=1-2*r+r*(q (A (u t)):ℝ)) :
    ∀ t : I,c≤t → ∀ w : BandWidth,
      G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
         ⟨δ*width*(w:ℝ),by
           have hs : 0<δ*width ∧ δ*width≤1 :=
             ⟨mul_pos hδ.1 hw.1,(mul_le_mul_of_nonneg_left hw.2 hδ.1.le).trans (by simpa using hδ.2)⟩
           constructor <;> nlinarith [w.property.1,w.property.2,hs.1,hs.2]⟩)
        ∈ F '' Set.range T ↔ t=1 := by
  intro t ht w
  let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk (2*(u t:ℝ)-1) w,by
    have hx : |2*(u t:ℝ)-1|≤1 := abs_le.mpr ⟨by linarith [(u t).property.1],by linarith [(u t).property.2]⟩
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hx (abs_le.mpr w.property)⟩
  let zi : ↥(Plane.closedSquare 0 1) := ⟨(1/2:ℝ) • Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1),by
    have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
    have hy : |z.val 1|≤1 := (le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
    have hsign : |if flip then -(z.val 1) else z.val 1|≤1 := by split_ifs <;> simpa using hy
    have hxx : |(1/2:ℝ)*z.val 0|≤1 := by rw [abs_mul]; norm_num; linarith only [hx]
    have hyy : |(1/2:ℝ)*(if flip then -(z.val 1) else z.val 1)|≤1 := by
      rw [abs_mul]; norm_num; linarith only [hsign]
    cases flip <;> simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hxx hyy⟩
  obtain ⟨v,hv,hvx,hvy⟩ := hE zi
  obtain ⟨t',w',v',ht',hw',hvx',hvy',hFn⟩ := hnative z
  have hteq : t'=u t := by apply Subtype.ext; simpa [z,Plane.mk] using ht'
  have hweq : (w':ℝ)=width*(w:ℝ) := by simpa [z,Plane.mk] using hw'
  have hveq : v=v' := by
    as_aux_lemma =>
      apply Prod.ext <;> apply Subtype.ext
      · change (v.1:ℝ)=(v'.1:ℝ)
        have hh : (v.1:ℝ)=((1/2:ℝ)*(if flip then -(z.val 1) else z.val 1))/2 := hvx
        nlinarith only [hh,hvx']
      · change (v.2:ℝ)=(v'.2:ℝ)
        have hh : (v.2:ℝ)=center+span*(2*((1/2:ℝ)*z.val 0)) := hvy
        nlinarith only [hh,hvy']
  have hmatch : F (E zi)=G
      (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
       ⟨δ*width*(w:ℝ),by
         have hs : 0<δ*width ∧ δ*width≤1 :=
           ⟨mul_pos hδ.1 hw.1,(mul_le_mul_of_nonneg_left hw.2 hδ.1.le).trans (by simpa using hδ.2)⟩
         constructor <;> nlinarith [w.property.1,w.property.2,hs.1,hs.2]⟩) := by
    rw [←hv,hveq,hFn,hteq,hC]
    congr 1
    apply Prod.ext <;> apply Subtype.ext
    · exact (hparam t ht).symm
    · change δ*(w':ℝ)=δ*width*(w:ℝ)
      rw [hweq]; ring
  rw [←hmatch]
  have hmem : F (E zi)∈F '' Set.range T ↔ E zi∈Set.range T := by
    constructor
    · rintro ⟨x,hx,he⟩
      exact F.injective he ▸ hx
    · intro hx; exact Set.mem_image_of_mem F hx
  rw [hmem,hsep zi]
  · have hz0 : zi.val 0=(2*(u t:ℝ)-1)/2 := by dsimp [zi,z,Plane.mk]; ring
    rw [hz0]
    have hzero : (2*(u t:ℝ)-1)/2=0 ↔ u t=⟨1/2,by norm_num⟩ := by
      constructor
      · intro he; apply Subtype.ext; change (u t:ℝ)=1/2; linarith
      · intro he; rw [he]; norm_num
    exact hzero.trans (hu1 t ht)
  · change 0≤(1/2:ℝ)*(2*(u t:ℝ)-1)
    have huR : (1/2:ℝ)≤(u t:ℝ) := hu t ht
    linarith
  · change |(1/2:ℝ)*(if flip then -(w:ℝ) else (w:ℝ))|≤1/2
    rw [abs_mul]
    have hwabs : |if flip then -(w:ℝ) else (w:ℝ)|≤1 := by split_ifs <;> simpa using abs_le.mpr w.property
    norm_num
    linarith

private theorem outsideBandsPackaging_3595_parameters (A : I ≃ₜ I) (hAmono : StrictMono A) (s : ℝ) (hs : 0 < s ∧ s ≤ 1/2)
    (r : ℝ) (hr : 0 < r ∧ r < 1/4) :
    ∃ τ : I, 0<τ ∧ τ<1 ∧
      (τ:ℝ)=1-2*r+r*s*(1-2*(A ⟨1/2,by norm_num⟩:ℝ)) ∧
    ∃ c : I, 0<c ∧ c<1 ∧
    ∃ u : I → I,
      (∀ t : I,c≤t → (A (u t):ℝ)=
        (1-(((τ:ℝ)*t-1+2*r)/r)/s)/2) ∧
      (∀ t : I,c≤t → ⟨1/2,by norm_num⟩≤u t) ∧
      (∀ t : I,c≤t → (u t=⟨1/2,by norm_num⟩ ↔ t=1)) ∧
      ∀ t : I,c≤t →
        (τ:ℝ)*t=1-2*r+r*s*(1-2*(A (u t):ℝ)) := by
  let half : I := ⟨1/2,by norm_num⟩
  let upper : I := ⟨3/4,by norm_num⟩
  let v := A half
  let w := A upper
  have hvw : (v:ℝ)<w := hAmono (show half<upper by norm_num [half,upper])
  have bounds (t : I) : 0 < 1-2*r+r*s*(1-2*(t:ℝ)) ∧
      1-2*r+r*s*(1-2*(t:ℝ)) < 1 := by
    as_aux_lemma =>
      have htlo : -1≤1-2*(t:ℝ) := by linarith [t.property.2]
      have hthi : 1-2*(t:ℝ)≤1 := by linarith [t.property.1]
      have hlo := mul_le_mul_of_nonneg_left htlo hs.1.le
      have hhi := mul_le_mul_of_nonneg_left hthi hs.1.le
      have hrlo := mul_le_mul_of_nonneg_left hlo hr.1.le
      have hrhi := mul_le_mul_of_nonneg_left hhi hr.1.le
      have hrsbound := mul_le_mul_of_nonneg_left hs.2 hr.1.le
      constructor <;> nlinarith only [hrlo,hrhi,hrsbound,hr.1,hr.2]
  let τ : I := ⟨1-2*r+r*s*(1-2*(v:ℝ)),⟨(bounds v).1.le,(bounds v).2.le⟩⟩
  have hτ0 : 0<τ := (bounds v).1
  have hτ1 : τ<1 := (bounds v).2
  let τc := 1-2*r+r*s*(1-2*(w:ℝ))
  have hτc0 : 0<τc := (bounds w).1
  have hτcτ : τc<(τ:ℝ) := by
    have hrs : 0<r*s := mul_pos hr.1 hs.1
    have hh := mul_lt_mul_of_pos_left (show 1-2*(w:ℝ)<1-2*(v:ℝ) by linarith) hrs
    change 1-2*r+r*s*(1-2*(w:ℝ))<1-2*r+r*s*(1-2*(v:ℝ))
    linarith
  let c : I := ⟨τc/(τ:ℝ),⟨(div_pos hτc0 hτ0).le,(div_le_one (show 0<(τ:ℝ) from hτ0)).mpr hτcτ.le⟩⟩
  have hc0 : 0<c := div_pos hτc0 hτ0
  have hc1 : c<1 := (div_lt_one (show 0<(τ:ℝ) from hτ0)).mpr hτcτ
  let value : I → ℝ := fun t => (1-(((τ:ℝ)*t-1+2*r)/r)/s)/2
  have hval (t : I) : (τ:ℝ)*t=1-2*r+r*s*(1-2*value t) := by dsimp [value]; field_simp [hr.1.ne',hs.1.ne']; ring
  have hv (t : I) (ht : c≤t) : (v:ℝ)≤value t ∧ value t≤w := by
    as_aux_lemma =>
      have htc : τc≤(τ:ℝ)*t := by
        have htcR : τc/(τ:ℝ)≤(t:ℝ) := ht
        have hh := (div_le_iff₀ (show 0<(τ:ℝ) from hτ0)).mp htcR
        rw [mul_comm (t:ℝ) (τ:ℝ)] at hh
        exact hh
      have htτ : (τ:ℝ)*t≤τ := by
        exact (mul_le_mul_of_nonneg_left t.property.2 (show 0≤(τ:ℝ) from hτ0.le)).trans_eq (mul_one _)
      have hh := hval t
      have hrs : 0<r*s := mul_pos hr.1 hs.1
      change 1-2*r+r*s*(1-2*(w:ℝ))≤(τ:ℝ)*t at htc
      change (τ:ℝ)*t≤1-2*r+r*s*(1-2*(v:ℝ)) at htτ
      constructor <;> nlinarith only [htc,htτ,hh,hrs]
  let u : I → I := fun t => A.symm (projIcc 0 1 zero_le_one (value t))
  have hAu (t : I) (ht : c≤t) : (A (u t):ℝ)=value t := by
    have hv' := hv t ht
    have hvalue : value t ∈ I := ⟨v.property.1.trans hv'.1,hv'.2.trans w.property.2⟩
    dsimp [u]
    rw [A.apply_symm_apply,projIcc_of_mem zero_le_one hvalue]
  refine ⟨τ,hτ0,hτ1,rfl,c,hc0,hc1,u,hAu,?_,?_,?_⟩
  · intro t ht
    apply hAmono.le_iff_le.mp
    change A half≤A (u t)
    change (v:ℝ)≤(A (u t):ℝ)
    rw [hAu t ht]
    exact (hv t ht).1
  · intro t ht
    constructor
    · intro hu
      have he := hAu t ht
      rw [hu] at he
      have hvv : value t=(v:ℝ) := he.symm
      have hh := hval t
      rw [hvv] at hh
      have heτ : (τ:ℝ)*t=(τ:ℝ)*1 := by exact hh.trans (by simp [τ])
      apply Subtype.ext
      exact mul_left_cancel₀ (show (τ:ℝ)≠0 from ne_of_gt (show 0<(τ:ℝ) from hτ0)) heτ
    · intro ht1
      apply A.injective
      apply Subtype.ext
      rw [hAu t ht]
      have hh := hval t
      rw [ht1] at hh
      have hone : ((1:I):ℝ)=1 := rfl
      rw [hone,mul_one] at hh
      rw [ht1]
      change value 1=(v:ℝ)
      have hrs : 0<r*s := mul_pos hr.1 hs.1
      change 1-2*r+r*s*(1-2*(v:ℝ))=1-2*r+r*s*(1-2*value 1) at hh
      nlinarith only [hh,hrs]
  · intro t ht
    rw [hAu t ht]
    exact hval t

private theorem outsideBandsPackaging_2244_bounded (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : ↥(Plane.closedSquare 0 1) → Plane, IsEmbedding C ∧
        Set.range C ⊆ Plane.openSquare 0 2 ∧
        (∀ t : Icc (-1 : ℝ) 1,
          C ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0) ∧
        (Set.range C ∩ {z : Plane | z 1 = 0} =
          (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) ∧
        ∀ z, C z = B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
          have hz : max |z.val 0| |z.val 1| ≤ 1 := by
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
          have hx := (le_max_left _ _).trans hz
          have hy := (le_max_right _ _).trans hz
          simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
            max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
  let Q := Plane.closedSquare 0 1
  let W := Icc (-1 : ℝ) 1
  let : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let : CompactSpace W := isCompact_iff_compactSpace.mp isCompact_Icc
  let J : W × W → Q := fun z => ⟨Plane.mk z.1 z.2,by
    simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using
      max_le (abs_le.mpr z.1.property) (abs_le.mpr z.2.property)⟩
  have hJ : Continuous J := by dsimp [J]; fun_prop
  let O := (B ∘ J) ⁻¹' Plane.openSquare 0 2
  have hO : IsOpen O := (Plane.isOpen_openSquare 0 2).preimage (hB.continuous.comp hJ)
  have haxis : (univ : Set W) ×ˢ ({⟨0,by norm_num [W]⟩} : Set W) ⊆ O := by
    as_aux_lemma =>
      rintro ⟨x,y⟩ ⟨_,hy⟩
      have he : y = ⟨0,by norm_num [W]⟩ := mem_singleton_iff.mp hy
      subst y
      change B (J (x,⟨0,by norm_num [W]⟩)) ∈ Plane.openSquare 0 2
      rw [hc]
      have hx := abs_le.mpr x.property
      simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using
        max_lt (lt_of_le_of_lt hx (by norm_num)) (by norm_num : |(0:ℝ)| < 2)
  obtain ⟨A,V,hA,hV,hWA,h0V,hAV⟩ :=
    generalized_tube_lemma isCompact_univ isCompact_singleton hO haxis
  obtain ⟨d,hd,hdV⟩ := Metric.mem_nhds_iff.mp
    (hV.mem_nhds (h0V (mem_singleton _)))
  let δ := min (d/2) 1
  have hδ0 : 0 < δ := lt_min (half_pos hd) (by norm_num)
  have hδ1 : δ ≤ 1 := min_le_right _ _
  have hδd : δ < d := (min_le_left _ _).trans_lt (half_lt_self hd)
  let k : Q → Q := fun z => ⟨Plane.mk (z.val 0) (δ*z.val 1),by
    have hz : max |z.val 0| |z.val 1| ≤ 1 := by
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
    have hx := (le_max_left _ _).trans hz
    have hy := (le_max_right _ _).trans hz
    simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ0] using
      max_le hx ((mul_le_mul_of_nonneg_left hy hδ0.le).trans (by simpa using hδ1))⟩
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    as_aux_lemma =>
      intro z w he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · simpa [k,Plane.mk] using congrArg (fun q : Q => q.val 0) he
      · have hy := congrArg (fun q : Q => q.val 1) he
        exact mul_left_cancel₀ hδ0.ne' hy
  let C := B ∘ k
  have hC : IsEmbedding C := hB.comp (hkc.isClosedEmbedding hki).isEmbedding
  have hCU : Set.range C ⊆ Plane.openSquare 0 2 := by
    as_aux_lemma =>
      rintro x ⟨z,rfl⟩
      have hz : max |z.val 0| |z.val 1| ≤ 1 := by
        simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
      let u : W := ⟨z.val 0,abs_le.mp ((le_max_left _ _).trans hz)⟩
      let v : W := ⟨δ*z.val 1,by
        have hh := (mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hz) hδ0.le).trans (by simpa using hδ1)
        exact abs_le.mp (by simpa [abs_mul,abs_of_pos hδ0] using hh)⟩
      have hv : v ∈ V := by
        apply hdV
        change dist v (⟨0,by norm_num [W]⟩ : W) < d
        rw [Subtype.dist_eq,Real.dist_eq]
        change |δ*z.val 1-0| < d
        rw [sub_zero,abs_mul,abs_of_pos hδ0]
        exact ((mul_le_mul_of_nonneg_left ((le_max_right _ _).trans hz) hδ0.le).trans (by simp)).trans_lt hδd
      have hh : (u,v) ∈ O := hAV ⟨hWA (mem_univ u),hv⟩
      exact hh
  have hCc (t : W) : C ⟨Plane.mk t 0,by
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0 := by
    as_aux_lemma =>
      change B (k _) = _
      have hk : k ⟨Plane.mk t 0,by
          simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
          ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
        apply Subtype.ext
        ext i
        fin_cases i <;> simp [k]
      rw [hk,hc]
  refine ⟨δ,⟨hδ0,hδ1⟩,C,hC,hCU,hCc,?_,fun _ => rfl⟩
  apply Set.Subset.antisymm
  · rintro x ⟨⟨z,rfl⟩,hx⟩
    exact hmeet ▸ (show C z ∈ Set.range B ∩ {z : Plane | z 1 = 0} from
      ⟨Set.mem_range_self (k z),hx⟩)
  · rintro x ⟨t,_,rfl⟩
    exact ⟨⟨⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩,hCc t⟩,by simp [Plane.mk]⟩

private theorem outsideBandsPackaging_3282_lift {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    (E : ↥(Plane.closedSquare 0 1) → S) (hE : IsEmbedding E)
    (H : Plane ≃ₜ Plane)
    (hfix : ∀ z, z ∉ Plane.openSquare 0 1 → H z=z) :
    ∃ F : S ≃ₜ S,
      (∀ z : ↥(Plane.closedSquare 0 1), F (E z)=E ⟨H z,by
        by_contra hh
        have ho : H z ∉ Plane.openSquare 0 1 := fun hz => hh ((Plane.openSquare_subset_closedSquare 0 1) hz)
        have he : H (H z)=H z := hfix _ ho
        have he' : H z=z := H.injective he
        exact hh (he'.symm ▸ z.property)⟩) ∧
      (∀ x, x ∉ interior (Set.range E) → F x=x) := by
  classical
  have patch (A : Set S) (hA : IsClosed A)
    (e : A ≃ₜ A) (he : ∀ x : A, (x:S) ∈ frontier A → (e x:S)=x) :
    ∃ H : S ≃ₜ S, (∀ x : A, H x=e x) ∧
      (∀ x, x ∉ interior A → H x=x) := by
    as_aux_lemma =>
      classical
      let C := (interior A)ᶜ
      have hC : IsClosed C := isOpen_interior.isClosed_compl
      have ha : ∀ x (hx : x∈A) (hc : x∈C), (e ⟨x,hx⟩:S)=x := by
        intro x hx hc
        apply he
        rw [frontier,hA.closure_eq]
        exact ⟨hx,hc⟩
      have hb : ∀ x (hx : x∈A) (hc : x∈C), (e.symm ⟨x,hx⟩:S)=x := by
        intro x hx hc
        have hh : e ⟨x,hx⟩=⟨x,hx⟩ := Subtype.ext (ha x hx hc)
        have hi := congrArg e.symm hh
        simpa using congrArg Subtype.val hi.symm
      let G := Schoenflies.ClosedCoverHomeomorph.glue hA hC hA hC e
        (Homeomorph.refl C) ha hb
      have hcover : A ∪ C=univ := by
        ext x
        simp only [mem_union,mem_univ,iff_true]
        by_cases hx : x∈interior A
        · exact Or.inl (interior_subset hx)
        · exact Or.inr hx
      let J : (A∪C : Set S) ≃ₜ S := (Homeomorph.setCongr hcover).trans (Homeomorph.Set.univ S)
      let H := J.symm.trans (G.trans J)
      have hj : ∀ x : (A∪C : Set S), J x=(x:S) := fun _ => rfl
      have hjs : ∀ x : S, (J.symm x:S)=x := by
        intro x
        exact (hj (J.symm x)).symm.trans (J.apply_symm_apply x)
      refine ⟨H,?_,?_⟩
      · intro x
        have hx : (J.symm (x:S):S)∈A := by rw [hjs]; exact x.property
        change J (G (J.symm (x:S)))=(e x:S)
        rw [hj,Schoenflies.ClosedCoverHomeomorph.coe_glue_apply_of_mem_left hA hC hA hC e (Homeomorph.refl C) ha hb _ hx]
        congr 1
      · intro x hx
        have hc : (J.symm x:S)∈C := by rw [hjs]; exact hx
        change J (G (J.symm x))=x
        rw [hj,Schoenflies.ClosedCoverHomeomorph.coe_glue_apply_of_mem_right hA hC hA hC e (Homeomorph.refl C) ha hb _ hc]
        exact hjs x

  let Q := Plane.closedSquare 0 1
  let : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  have hm : H '' Q=Q := by
    as_aux_lemma =>
      ext z
      constructor
      · rintro ⟨x,hx,rfl⟩
        by_contra hh
        have ho : H x ∉ Plane.openSquare 0 1 := fun hz => hh ((Plane.openSquare_subset_closedSquare 0 1) hz)
        have he : H (H x)=H x := hfix _ ho
        have he' : H x=x := H.injective he
        exact hh (he'.symm ▸ hx)
      · intro hz
        refine ⟨H.symm z,?_,H.apply_symm_apply z⟩
        by_contra hh
        have ho : H.symm z ∉ Plane.openSquare 0 1 := fun hx => hh ((Plane.openSquare_subset_closedSquare 0 1) hx)
        have he : H (H.symm z)=H.symm z := hfix _ ho
        have he' : z=H.symm z := (H.apply_symm_apply z).symm.trans he
        exact hh (he' ▸ hz)
  let P : Q ≃ₜ Q := (H.image Q).trans (Homeomorph.setCongr hm)
  let J := hE.toHomeomorph
  let C := J.symm.trans (P.trans J)
  have hc : ∀ z : Q, (C (J z):S)=E (P z) := by
    intro z
    change (J (P (J.symm (J z))):S)=E (P z)
    rw [J.symm_apply_apply]
    rfl
  have hfront : ∀ x : Set.range E, (x:S) ∈ frontier (Set.range E) → (C x:S)=x := by
    as_aux_lemma =>
      intro x hx
      have hh : (x:S) ∈ E '' {z : Q | (z:Plane) ∈ frontier Q} := by
        rw [embedded_compact_planar_region_frontier_probe Q (isCompact_closedSquare 0 1) E hE]
        exact hx
      obtain ⟨z,hz,he⟩ := hh
      have hJ : J z=x := Subtype.ext he
      rw [←hJ,hc]
      have hP : P z=z := by
        apply Subtype.ext
        apply hfix
        rw [←Plane.interior_closedSquare]
        exact hz.2
      rw [hP]
      rfl
  obtain ⟨F,hFc,hFfix⟩ := patch (Set.range E) (isCompact_range hE.continuous).isClosed C hfront
  refine ⟨F,?_,hFfix⟩
  intro z
  exact (hFc (J z)).trans (hc z)

private theorem outsideBandsPackaging_4690_paste {S : Type} [TopologicalSpace S] [T2Space S]
    {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (L R : I × BandWidth → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
    (hseam : ∀ w,L (1,w)=R (0,w))
    (hmeet : Set.range L ∩ Set.range R=Set.range (fun w => L (1,w)))
    (haxisL : ∀ z,L z∈Set.range p ↔ (z.2:ℝ)=0)
    (haxisR : ∀ z,R z∈Set.range p ↔ (z.2:ℝ)=0)
    (hcover : Set.range p ⊆ Set.range L ∪ Set.range R)
    (hstart : L (0,⟨0,by norm_num⟩)=p 0)
    (hend : R (1,⟨0,by norm_num⟩)=p 1) :
    ∃ G : I × BandWidth → S,IsEmbedding G ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=p t) ∧
      (∀ w,G (0,w)=L (0,w)) ∧ (∀ w,G (1,w)=R (1,w)) ∧
      Set.range G=Set.range L ∪ Set.range R ∧
      ∀ z,G z∈Set.range p ↔ (z.2:ℝ)=0 := by
  let L' : I × BandWidth → S := fun z => L (unitInterval.symm z.1,z.2)
  have hLc : Continuous L' := hL.continuous.comp
    ((unitInterval.continuous_symm.comp continuous_fst).prodMk continuous_snd)
  have hLi : Function.Injective L' := by
    intro z w he
    have hh := hL.injective he
    apply Prod.ext
    · exact unitInterval.symm_involutive.injective (congrArg Prod.fst hh)
    · have hh2 : z.2=w.2 := Prod.mk.inj hh |>.2
      exact hh2
  have hL' : IsEmbedding L' := (hLc.isClosedEmbedding hLi).isEmbedding
  have hLrange : Set.range L'=Set.range L := by
    apply Set.Subset.antisymm
    · rintro x ⟨z,rfl⟩; exact Set.mem_range_self _
    · rintro x ⟨z,rfl⟩
      exact ⟨(unitInterval.symm z.1,z.2),by simp [L']⟩
  have hL0 (w : BandWidth) : L' (0,w)=R (0,w) := by simpa [L'] using hseam w
  have hmeet' : Set.range L' ∩ Set.range R=Set.range (fun w => L' (0,w)) := by
    rw [hLrange,hmeet]
    congr 1
    funext w
    simp [L']
  obtain ⟨E,hE,hE0,hE1,_,hErange,htrack⟩ :=
    source_glue_two_surface_strips L' R hL' hR hL0 hmeet'
  have hEaxis (z : I × BandWidth) : E z∈Set.range p ↔ (z.2:ℝ)=0 := by
    obtain ⟨t,ht | ht⟩ := htrack z
    · rw [ht]
      exact haxisL (unitInterval.symm t,z.2)
    · rw [ht]
      exact haxisR (t,z.2)
  have hcenterrange : Set.range (fun t : I => E (t,⟨0,by norm_num⟩))=Set.range p := by
    as_aux_lemma =>
      apply Set.Subset.antisymm
      · rintro x ⟨t,rfl⟩
        exact (hEaxis (t,⟨0,by norm_num⟩)).mpr rfl
      · intro x hx
        have hxE : x∈Set.range E := by
          rw [hErange,hLrange]
          exact hcover hx
        obtain ⟨z,rfl⟩ := hxE
        have hz : z.2=⟨0,by norm_num⟩ := Subtype.ext ((hEaxis z).mp hx)
        exact ⟨z.1,by rw [←hz]⟩
  have normalize {S : Type} [TopologicalSpace S] [T2Space S]
      {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (E : I × BandWidth → S) (hE : IsEmbedding E)
      (hcenterrange : Set.range (fun t : I => E (t,⟨0,by norm_num⟩)) = Set.range p)
      (h0 : E (0,⟨0,by norm_num⟩)=p 0)
      (h1 : E (1,⟨0,by norm_num⟩)=p 1) :
      ∃ A : I ≃ₜ I, A 0=0 ∧ A 1=1 ∧
      ∃ F : I × BandWidth → S, IsEmbedding F ∧
        (∀ t : I,F (t,⟨0,by norm_num⟩)=p t) ∧
        (∀ w,F (0,w)=E (0,w)) ∧ (∀ w,F (1,w)=E (1,w)) ∧
        Set.range F=Set.range E ∧ ∀ z,F z=E (A z.1,z.2) := by
    apply outsideBandsPackaging_4746_normalize <;> assumption
  have hEstart : E (0,⟨0,by norm_num⟩)=p 0 := by
    rw [hE0]
    simpa [L'] using hstart
  obtain ⟨A,hA0,hA1,G,hG,hGc,hG0,hG1,hGrange,hformula⟩ :=
    normalize p hp E hE hcenterrange hEstart ((hE1 _).trans hend)
  refine ⟨G,hG,hGc,?_,?_,?_,?_⟩
  · intro w
    rw [hG0,hE0]
    simp [L']
  · intro w
    exact (hG1 w).trans (hE1 w)
  · rw [hGrange,hErange,hLrange]
  · intro z
    rw [hformula]
    exact hEaxis (A z.1,z.2)

private theorem outsideBandsPackaging_228_initial {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {a b : Curve S} (D : OneCrossingBandBase a b)
    (m : I) (hm0 : 0 < m) (hm1 : m < 1)
    (hmends : D.firstArc '' Icc 0 m ⊆ Set.range (D.ends 2)) :
    ∃ E : I × BandWidth → S, IsEmbedding E ∧
      (∀ w, E (0,w) = D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩) = D.firstArc.extend ((m : ℝ)*t)) ∧
      Set.range E ∩ Set.range D.firstArc = D.firstArc '' Icc 0 m ∧
      Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range E) (Set.range D.secondArc) ∧ Set.range E ⊆ Set.range (D.ends 2) := by
  classical
  have hmR : 0 < (m : ℝ) := hm0
  let s : I → I := fun t => ⟨(m : ℝ)*t,by constructor <;> nlinarith [t.property.1,t.property.2,m.property.1,m.property.2]⟩
  have hsc : Continuous s := by dsimp [s]; fun_prop
  have hsI (t : I) : s t ∈ Icc 0 m := ⟨(s t).property.1,by change (m : ℝ)*t ≤ m; nlinarith [t.property.2]⟩
  have hs0 : s 0 = 0 := by apply Subtype.ext; simp [s]
  let A := (D.ends_embedded 2).toHomeomorph
  let u : I → Set.range (D.ends 2) := fun t => ⟨D.firstArc (s t),hmends ⟨s t,hsI t,rfl⟩⟩
  have huc : Continuous u := Continuous.subtype_mk (D.firstArc.continuous.comp hsc) _
  let g : I → EndRectangle := A.symm ∘ u
  have hgc : Continuous g := A.symm.continuous.comp huc
  have hforward (t : I) : D.ends 2 (g t) = D.firstArc (s t) := by
    have hh := congrArg Subtype.val (A.apply_symm_apply (u t))
    exact hh
  have hgfirst (t : I) : (g t).1 = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    have haxis := (D.ends_axes 2 (g t)).1
    have hmem : D.firstArc (s t) ∈ a.image := by
      have hh : D.firstArc (s t) ∈ a.image \ D.openSquare := D.firstArc_range ▸ Set.mem_range_self _
      exact hh.1
    exact (haxis.mp ((hforward t).symm ▸ hmem)).2
  have hg0 : g 0 = (⟨0,by norm_num⟩,⟨0,by norm_num⟩) := by
    apply (D.ends_embedded 2).injective
    rw [hforward,hs0,D.firstArc.source,D.ends_seam]
  have heighti : Function.Injective (fun t => (g t).2) := by
    as_aux_lemma =>
      intro t v he
      have he' : g t = g v := Prod.ext ((hgfirst t).trans (hgfirst v).symm) he
      have hh := congrArg (D.ends 2) he'
      rw [hforward,hforward] at hh
      have hs := D.firstArc_embedded.injective hh
      apply Subtype.ext
      have hsR := congrArg Subtype.val hs
      change (m : ℝ)*t=(m : ℝ)*v at hsR
      exact mul_left_cancel₀ hmR.ne' hsR
  let E : I × BandWidth → S := fun z => D.ends 2 (z.2,(g z.1).2)
  have hEc : Continuous E := (D.ends_embedded 2).continuous.comp (continuous_snd.prodMk ((hgc.comp continuous_fst).snd))
  have hEi : Function.Injective E := by
    intro z w he
    have hh := (D.ends_embedded 2).injective he
    apply Prod.ext
    · have hh' := congrArg Prod.snd hh
      exact heighti hh' 
    · exact congrArg Prod.fst hh
  have hE : IsEmbedding E := (hEc.isClosedEmbedding hEi).isEmbedding
  have hE0 (w : BandWidth) : E (0,w) = D.square (squarePort D.radius D.radius_pos 2 w) := by
    change D.ends 2 (w,(g 0).2) = _
    rw [hg0,D.ends_seam]
  have hEc0 (t : I) : E (t,⟨0,by norm_num⟩) = D.firstArc (s t) := by
    change D.ends 2 (⟨0,by norm_num⟩,(g t).2) = _
    have he : (⟨0,by norm_num⟩,(g t).2) = g t := Prod.ext (hgfirst t).symm rfl
    exact (congrArg (D.ends 2) he).trans (hforward t)
  have hcenter (t : I) : E (t,⟨0,by norm_num⟩) = D.firstArc.extend ((m : ℝ)*t) := by
    rw [hEc0]
    exact (D.firstArc.extend_apply (s t).property).symm
  have hmeet : Set.range E ∩ Set.range D.firstArc = D.firstArc '' Icc 0 m := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨⟨z,rfl⟩,⟨v,hv⟩⟩
        have hmem : E z ∈ a.image := by
          rw [← hv]
          have hh : D.firstArc v ∈ a.image \ D.openSquare := D.firstArc_range ▸ Set.mem_range_self _
          exact hh.1
        have hw : z.2 = ⟨0,by norm_num⟩ := by
          apply Subtype.ext
          exact ((D.ends_axes 2 (z.2,(g z.1).2)).1.mp hmem).2
        have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl hw
        rw [he,hEc0]
        exact ⟨s z.1,hsI z.1,rfl⟩
      · rintro ⟨v,hv,rfl⟩
        let t : I := ⟨(v : ℝ)/m,⟨div_nonneg v.property.1 hmR.le,(div_le_one hmR).mpr (show (v : ℝ) ≤ m from hv.2)⟩⟩
        have ht : s t = v := by apply Subtype.ext; exact mul_div_cancel₀ _ hmR.ne'
        refine ⟨⟨(t,⟨0,by norm_num⟩),?_⟩,Set.mem_range_self _⟩
        rw [hEc0,ht]
  have hheightzero (t : I) (ht : ((g t).2 : ℝ) ≤ 0) : t = 0 := by
    as_aux_lemma =>
      have hQ : D.firstArc (s t) ∈ Set.range D.square := by
        rw [← hEc0]
        exact (D.ends_square 2 (⟨0,by norm_num⟩,(g t).2)).mpr ht
      have hh : D.firstArc (s t) ∈ ({D.firstArc 0,D.firstArc 1} : Set S) :=
        D.firstArc_square_intersection ▸ ⟨Set.mem_range_self _,hQ⟩
      rcases Set.mem_insert_iff.mp hh with he0 | he1
      · have hs := D.firstArc_embedded.injective he0
        have hsR := congrArg Subtype.val hs
        apply Subtype.ext
        change (m : ℝ)*t=0 at hsR
        exact (mul_eq_zero.mp hsR).resolve_left hmR.ne'
      · have he1' : D.firstArc (s t) = D.firstArc 1 := he1
        have hs := D.firstArc_embedded.injective he1'
        have hsR := congrArg Subtype.val hs
        change (m : ℝ)*t=1 at hsR
        have hb := mul_le_mul_of_nonneg_left t.property.2 m.property.1
        have hm1R : (m : ℝ)<1 := hm1
        linarith
  have hE_Q : Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨⟨z,rfl⟩,hzQ⟩
        have hz0 := hheightzero z.1 ((D.ends_square 2 (z.2,(g z.1).2)).mp hzQ)
        refine ⟨z.2,?_⟩
        have he : z = (0,z.2) := Prod.ext hz0 rfl
        rw [he,hE0]
      · rintro ⟨w,rfl⟩
        exact ⟨⟨(0,w),hE0 w⟩,Set.mem_range_self _⟩
  refine ⟨E,hE,hE0,hcenter,hmeet,hE_Q,?_,?_⟩
  · apply Set.disjoint_left.mpr
    rintro q ⟨z,rfl⟩ hqsecond
    have hmem : E z ∈ b.image := by
      have hh : E z ∈ b.image \ D.openSquare := D.secondArc_range ▸ hqsecond
      exact hh.1
    have hh := ((D.ends_axes 2 (z.2,(g z.1).2)).2.mp hmem).1
    norm_num at hh
  · rintro q ⟨z,rfl⟩
    exact Set.mem_range_self (z.2,(g z.1).2)

private theorem outsideBandsPackaging_2105_normalize (C : I × Icc (-1 : ℝ) 1 → Plane) (hC : IsEmbedding C)
    (height : I → ℝ) (hh : Continuous height) (hm : StrictMono height)
    (hc : ∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
    (haxis : ∀ z, C z 1=0 ↔ (z.2:ℝ)=0) :
    ∃ B : ↥(Plane.closedSquare 0 1) → Plane, IsEmbedding B ∧
      (∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0) ∧
      (Set.range B ∩ {z : Plane | z 1=0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) ∧
      ∃ A : I ≃ₜ I,
        (∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),
          B z=Plane.mk
            ((2*(C (A ⟨(z.val 0+1)/2,by
                have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
                constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩,
                ⟨z.val 1,abs_le.mp ((le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property))⟩) 0-height 0))/(height 1-height 0)-1)
            (C (A ⟨(z.val 0+1)/2,by
                have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
                constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩,
                ⟨z.val 1,abs_le.mp ((le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property))⟩) 1) := by
  classical
  have reparam (h : I → ℝ) (hc : Continuous h) (hm : StrictMono h) :
    ∃ A : I ≃ₜ I, ∀ t : I, h (A t)=h 0+(h 1-h 0)*(t:ℝ) := by
    apply outsideBandsPackaging_2127_reparam <;> assumption
  obtain ⟨A,hA⟩ := reparam height hh hm
  have hd : 0<height 1-height 0 := sub_pos.mpr (hm (by norm_num : (0:I)<1))
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let j : Q → I × Icc (-1 : ℝ) 1 := fun z =>
    (⟨(z.val 0+1)/2,by
      have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
      constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩,
     ⟨z.val 1,abs_le.mp ((le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property))⟩)
  let k : Q → I × Icc (-1 : ℝ) 1 := fun z => (A (j z).1,(j z).2)
  have hjc : Continuous j := by dsimp [j]; fun_prop
  have hkc : Continuous k := (A.continuous.comp hjc.fst).prodMk hjc.snd
  have hki : Function.Injective k := by
    as_aux_lemma =>
      intro z w he
      have ht := A.injective (congrArg Prod.fst he)
      have hw := congrArg Prod.snd he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · have hx := congrArg (fun t : I => (t:ℝ)) ht
        change (z.val 0+1)/2=(w.val 0+1)/2 at hx
        change z.val 0=w.val 0
        linarith
      · exact congrArg Subtype.val hw
  let N : Plane → Plane := fun z => Plane.mk ((2*(z 0-height 0))/(height 1-height 0)-1) (z 1)
  have hNc : Continuous N := by dsimp [N]; fun_prop
  have hNi : Function.Injective N := by
    as_aux_lemma =>
      intro z w he
      have hx := congrArg (fun z : Plane => z 0) he
      have hy := congrArg (fun z : Plane => z 1) he
      change 2*(z 0-height 0)/(height 1-height 0)-1=2*(w 0-height 0)/(height 1-height 0)-1 at hx
      have hdiv : 2*(z 0-height 0)=2*(w 0-height 0) := (div_left_inj' hd.ne').mp (by linarith : 2*(z 0-height 0)/(height 1-height 0)=2*(w 0-height 0)/(height 1-height 0))
      apply PiLp.ext
      intro i
      fin_cases i
      · change z 0=w 0
        linarith
      · exact hy
  let B : Q → Plane := N ∘ C ∘ k
  have hBc : Continuous B := hNc.comp (hC.continuous.comp hkc)
  have hBi : Function.Injective B := hNi.comp (hC.injective.comp hki)
  have hcenter (t : Icc (-1 : ℝ) 1) :
      B ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0 := by
    as_aux_lemma =>
      change N (C (A ⟨((t:ℝ)+1)/2,_⟩,⟨0,_⟩))=Plane.mk t 0
      rw [hc,hA]
      apply PiLp.ext
      intro i
      fin_cases i
      · change 2*(height 0+(height 1-height 0)*(((t:ℝ)+1)/2)-height 0)/(height 1-height 0)-1=t
        field_simp
        ring
      · rfl
  refine ⟨B,(hBc.isClosedEmbedding hBi).isEmbedding,hcenter,?_,A,hA,(fun _ => rfl)⟩
  ext z
  constructor
  · rintro ⟨⟨q,rfl⟩,hq⟩
    have hy : C (k q) 1=0 := hq
    have hw : q.val 1=0 := (haxis (k q)).mp hy
    let t : Icc (-1 : ℝ) 1 := ⟨q.val 0,abs_le.mp ((le_max_left _ _).trans (show max |q.val 0| |q.val 1|≤1 from by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using q.property))⟩
    have hqeq : q=⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · exact hw
    exact ⟨t,mem_univ _,(hqeq ▸ hcenter t).symm⟩
  · rintro ⟨t,_,rfl⟩
    refine ⟨⟨_,hcenter t⟩,?_⟩
    rfl

private theorem outsideBandsPackaging_2383_sides (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (haxis : ∀ z, B z 1=0 ↔ z.val 1=0)
    (hB0 : B ⟨0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ = 0) :
    ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∧
      (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0)) ∨
    ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) ∧
      (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → 0<B z 1)) := by
  have side (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (haxis : ∀ z, B z 1=0 ↔ z.val 1=0) :
      (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∨
      (∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) := by
    apply outsideBandsPackaging_2390_side <;> assumption
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let T : Q → Q := fun z => ⟨Plane.mk (z.val 0) (-z.val 1),by
    simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property⟩
  have hTc : Continuous T := by dsimp [T]; fun_prop
  have hTi : Function.Injective T := by
    as_aux_lemma =>
      intro z w he
      apply Subtype.ext
      have hx := congrArg (fun z : Q => z.val 0) he
      have hy := congrArg (fun z : Q => z.val 1) he
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hx
      · change -z.val 1 = -w.val 1 at hy
        exact neg_injective hy
  have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
  have hTT (z : Q) : T (T z) = z := by
    apply Subtype.ext
    apply PiLp.ext
    intro i
    fin_cases i <;> simp [T,Plane.mk]
  let B' : Q → Plane := B ∘ T
  have hB' : IsEmbedding B' := hB.comp hTe
  have haxis' (z : Q) : B' z 1=0 ↔ z.val 1=0 := by
    change B (T z) 1=0 ↔ z.val 1=0
    rw [haxis]
    change -z.val 1=0 ↔ z.val 1=0
    exact neg_eq_zero
  have hplus := side B hB haxis
  have hminus0 := side B' hB' haxis'
  have hminus : (∀ z : Q,z.val 1<0 → 0<B z 1) ∨ (∀ z : Q,z.val 1<0 → B z 1<0) := by
    as_aux_lemma =>
      rcases hminus0 with hp | hn
      · left
        intro z hz
        have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
        have hh := hp (T z) ht
        change B (T (T z)) 1>0 at hh
        rwa [hTT] at hh
      · right
        intro z hz
        have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
        have hh := hn (T z) ht
        change B (T (T z)) 1<0 at hh
        rwa [hTT] at hh
  have hzero : (0:Plane) ∈ interior Q := by
    rw [Plane.interior_closedSquare]
    simp [Plane.openSquare,Plane.supDist,Plane.supNorm]
  have hzeroim : (0:Plane) ∈ interior (Set.range B) := by
    have hh := (embedded_planar_region_interior_iff_probe Q B hB ⟨0,interior_subset hzero⟩).mpr hzero
    rwa [hB0] at hh
  obtain ⟨d,hd,hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hzeroim)
  have hpm (s : ℝ) (hs : s=1 ∨ s= -1) : Plane.mk 0 (s*d/2) ∈ Set.range B := by
    apply interior_subset
    apply hball
    rw [Metric.mem_ball,dist_zero_right]
    rcases hs with rfl | rfl <;> simp [Plane.mk,EuclideanSpace.norm_eq,Fin.sum_univ_two,Real.sqrt_sq_eq_abs,abs_mul,abs_div,abs_of_pos hd] <;> linarith
  obtain ⟨zp,hzp⟩ := hpm 1 (Or.inl rfl)
  obtain ⟨zn,hzn⟩ := hpm (-1) (Or.inr rfl)
  have hzpR : B zp 1=d/2 := by have hh := congrArg (fun z : Plane => z 1) hzp; simpa using hh
  have hznR : B zn 1= -d/2 := by have hh := congrArg (fun z : Plane => z 1) hzn; simpa using hh
  rcases hplus with hp | hn
  · rcases hminus with mp | mn
    · exfalso
      rcases lt_trichotomy (zn.val 1) 0 with hneg | heq | hpos
      · have hh := mp zn hneg; linarith
      · have hh := (haxis zn).mpr heq; linarith
      · have hh := hp zn hpos; linarith
    · exact Or.inl ⟨hp,mn⟩
  · rcases hminus with mp | mn
    · exact Or.inr ⟨hn,mp⟩
    · exfalso
      rcases lt_trichotomy (zp.val 1) 0 with hneg | heq | hpos
      · have hh := mn zp hneg; linarith
      · have hh := (haxis zp).mpr heq; linarith
      · have hh := hn zp hpos; linarith

private theorem outsideBandsPackaging_4966_taper {S : Type} [TopologicalSpace S] [T2Space S]
    (E : I × BandWidth → S) (hE : IsEmbedding E)
    (K : Set S) (hK : IsClosed K)
    (hcenter : ∀ t : I,E (t,⟨0,by norm_num⟩)∉K)
    (hbottom : ∀ w : BandWidth,E (0,w)∉K)
    (htop : ∀ w : BandWidth,E (1,w)∉K) :
    ∃ F : I × BandWidth → S, IsEmbedding F ∧
      (∀ t,F (t,⟨0,by norm_num⟩)=E (t,⟨0,by norm_num⟩)) ∧
      (∀ w,F (0,w)=E (0,w)) ∧ (∀ w,F (1,w)=E (1,w)) ∧
      Set.range F ⊆ Set.range E ∧ Disjoint (Set.range F) K := by
    classical
    let O := E ⁻¹' Kᶜ
    have hO : IsOpen O := hK.isOpen_compl.preimage hE.continuous
    have hcore : (univ : Set I) ×ˢ ({⟨0,by norm_num⟩} : Set BandWidth) ⊆ O := by
      rintro ⟨t,w⟩ ⟨_,hw⟩
      have he : w=⟨0,by norm_num⟩ := mem_singleton_iff.mp hw
      subst w
      exact hcenter t
    obtain ⟨A,V,hA,hV,hTA,h0V,hAV⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hO hcore
    obtain ⟨d,hd,hdV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton _)))
    have hend (i : I) (hi : i=0 ∨ i=1) : ({i} : Set I) ×ˢ (univ : Set BandWidth) ⊆ O := by
      rintro ⟨t,w⟩ ⟨ht,_⟩
      have he : t=i := mem_singleton_iff.mp ht
      subst t
      rcases hi with hi|hi
      · subst i; exact hbottom w
      · subst i; exact htop w
    obtain ⟨W,Q,hW,hQ,h0W,hUQ,hWQ⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ hO (hend 0 (Or.inl rfl))
    obtain ⟨b,hb,hbW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (h0W (mem_singleton _)))
    obtain ⟨U,Z,hU,hZ,h1U,hUZ,hUZsub⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ hO (hend 1 (Or.inr rfl))
    obtain ⟨c,hc,hcU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h1U (mem_singleton _)))
    let ε : ℝ := min (d/2) 1
    have hε : 0<ε := lt_min (half_pos hd) (by norm_num)
    have hε1 : ε≤1 := min_le_right _ _
    have hεd : ε<d := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hd)
    let scale : I → ℝ := fun t => max ε (max (1-(t:ℝ)/b) (1-(1-(t:ℝ))/c))
    have hsC : Continuous scale := by dsimp [scale]; fun_prop
    have hs (t : I) : 0<scale t ∧ scale t≤1 := by
      constructor
      · exact lt_of_lt_of_le hε (le_max_left _ _)
      · apply max_le hε1
        apply max_le
        · linarith [div_nonneg t.property.1 hb.le]
        · linarith [div_nonneg (sub_nonneg.mpr t.property.2) hc.le]
    have hs0 : scale 0=1 := by
      have hbound : 1-1/c≤1 := by linarith [div_nonneg (by norm_num : (0:ℝ)≤1) hc.le]
      change max ε (max (1-0/b) (1-(1-0)/c))=1
      simp only [zero_div,sub_zero]
      rw [max_eq_left hbound,max_eq_right hε1]
    have hs1 : scale 1=1 := by
      have hbound : 1-1/b≤1 := by linarith [div_nonneg (by norm_num : (0:ℝ)≤1) hb.le]
      change max ε (max (1-1/b) (1-(1-1)/c))=1
      simp only [sub_self,zero_div,sub_zero]
      rw [max_eq_right hbound,max_eq_right hε1]
    let k : I × BandWidth → I × BandWidth := fun z =>
      (z.1,⟨scale z.1*(z.2:ℝ),by
        have hst := hs z.1
        constructor <;> nlinarith [z.2.property.1,z.2.property.2]⟩)
    have hkc : Continuous k := by dsimp [k]; fun_prop
    have hki : Function.Injective k := by
      as_aux_lemma =>
        intro z w he
        have ht : z.1=w.1 := by simpa [k] using congrArg Prod.fst he
        apply Prod.ext ht
        apply Subtype.ext
        have hw := congrArg (fun q : I × BandWidth => (q.2:ℝ)) he
        change scale z.1*(z.2:ℝ)=scale w.1*(w.2:ℝ) at hw
        rw [←ht] at hw
        exact mul_left_cancel₀ (hs z.1).1.ne' hw
    let F := E ∘ k
    have hFc : Continuous F := hE.continuous.comp hkc
    have hFi : Function.Injective F := hE.injective.comp hki
    have havoid (z : I × BandWidth) : F z∉K := by
      as_aux_lemma =>
        by_cases hleft : (z.1:ℝ)<b
        · have htW : z.1∈W := by
            apply hbW
            change dist z.1 (0:I)<b
            rw [Subtype.dist_eq,Real.dist_eq]
            change |(z.1:ℝ)-0|<b
            simpa [abs_of_nonneg z.1.property.1] using hleft
          exact hWQ ⟨htW,hUQ (mem_univ _)⟩
        · by_cases hright : 1-(z.1:ℝ)<c
          · have htU : z.1∈U := by
              apply hcU
              change dist z.1 (1:I)<c
              rw [Subtype.dist_eq,Real.dist_eq]
              change |(z.1:ℝ)-1|<c
              rw [abs_of_nonpos (sub_nonpos.mpr z.1.property.2)]
              simpa using hright
            exact hUZsub ⟨htU,hUZ (mem_univ _)⟩
          · have hl : 1-(z.1:ℝ)/b≤0 := by
              have hh := (one_le_div hb).mpr (le_of_not_gt hleft)
              linarith
            have hr : 1-(1-(z.1:ℝ))/c≤0 := by
              have hh := (one_le_div hc).mpr (le_of_not_gt hright)
              linarith
            have hseq : scale z.1=ε := by
              change max ε (max (1-(z.1:ℝ)/b) (1-(1-(z.1:ℝ))/c))=ε
              exact max_eq_left ((max_le hl hr).trans hε.le)
            have hwV : (k z).2∈V := by
              apply hdV
              change dist (k z).2 (⟨0,by norm_num⟩ : BandWidth)<d
              rw [Subtype.dist_eq,Real.dist_eq,sub_zero]
              change |scale z.1*(z.2:ℝ)|<d
              rw [hseq,abs_mul,abs_of_pos hε]
              exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hε.le).trans (by simp)) hεd
            exact hAV ⟨hTA (mem_univ _),hwV⟩
    refine ⟨F,(hFc.isClosedEmbedding hFi).isEmbedding,?_,?_,?_,?_,?_⟩
    · intro t
      change E (k (t,⟨0,by norm_num⟩))=E (t,⟨0,by norm_num⟩)
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      simp [k]
    · intro w
      change E (k (0,w))=E (0,w)
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      change scale 0*w=w
      simp [hs0]
    · intro w
      change E (k (1,w))=E (1,w)
      congr 1
      apply Prod.ext
      · rfl
      apply Subtype.ext
      change scale 1*w=w
      simp [hs1]
    · rintro x ⟨z,rfl⟩
      exact Set.mem_range_self (k z)
    · apply Set.disjoint_left.mpr
      rintro x ⟨z,rfl⟩ hx
      exact havoid z hx

private theorem outsideBandsPackaging_767_narrow {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m : I) (h : ℝ) (hh : 0 < h ∧ (m : ℝ)+h ≤ 1)
    (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
    (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+h*t))
    (hpre : Set.range E ∩ p '' Icc 0 m = {p m})
    (k : ℝ) (hk : 0 < k ∧ k < 1) :
    ∃ lambda : ℝ, ∃ hl : 0 < lambda ∧ lambda ≤ 1,
      ∃ R : I × Icc (-1 : ℝ) 1 → S,
        (∀ z : I × Icc (-1 : ℝ) 1, R z = E
          (⟨k*z.1,by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hk.1,hk.2]⟩,
           ⟨lambda*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hl.1,hl.2]⟩)) ∧
        IsEmbedding R ∧ Set.range R ⊆ Set.range E ∧
        (∀ w : Icc (-1 : ℝ) 1, R (0,w) = E (0,⟨lambda*w,by
          constructor <;> nlinarith [w.property.1,w.property.2,hl.1,hl.2]⟩)) ∧
        (∀ t : I, R (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+(h*k)*t)) ∧
        Set.range R ∩ Set.range p = p '' Icc m
          ⟨(m : ℝ)+h*k,by constructor <;> nlinarith [m.property.1]⟩ := by
  classical
  let D := I × Icc (-1 : ℝ) 1
  have hkt (t : I) : 0 ≤ k*(t : ℝ) ∧ k*(t : ℝ) ≤ 1 := by
    constructor
    · exact mul_nonneg hk.1.le t.property.1
    · exact (mul_le_mul_of_nonneg_left t.property.2 hk.1.le).trans (by simpa using hk.2.le)
  have hupper (t : I) : (m : ℝ)+h*k*t ≤ 1 := by
    have he : h*k*(t : ℝ) = h*(k*t) := by ring
    rw [he]
    have hb := mul_le_mul_of_nonneg_left (hkt t).2 hh.1.le; nlinarith [hh.2]
  let n : I := ⟨(m : ℝ)+h,⟨by linarith [m.property.1],hh.2⟩⟩
  let a : D → D := fun z => (⟨k*z.1,by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hk.1,hk.2]⟩,z.2)
  have hac : Continuous a := by dsimp [a,D]; fun_prop
  have hai : Function.Injective a := by
    intro z w he
    apply Prod.ext
    · apply Subtype.ext
      have hh' := congrArg (fun z : D => (z.1 : ℝ)) he
      exact mul_left_cancel₀ hk.1.ne' hh'
    · simpa [a] using congrArg Prod.snd he
  let raw : D → S := E ∘ a
  have hraw : IsEmbedding raw := hE.comp ((hac.isClosedEmbedding hai).isEmbedding)
  have hrawcenter (t : I) : raw (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+(h*k)*t) := by
    rw [show raw (t,⟨0,by norm_num⟩) = E (⟨k*t,by constructor <;> nlinarith [t.property.1,t.property.2,hk.1,hk.2]⟩,⟨0,by norm_num⟩) from rfl,hcenter]
    congr 1; ring
  let K := p '' Ici n
  have hK : IsClosed K := (isClosed_Ici.isCompact.image hp.continuous).isClosed
  have havoid (t : I) : raw (t,⟨0,by norm_num⟩) ∉ K := by
    as_aux_lemma =>
      rintro ⟨s,hs,he⟩
      let u : I := ⟨(m : ℝ)+h*k*t,by constructor; exact add_nonneg m.property.1 (mul_nonneg (mul_pos hh.1 hk.1).le t.property.1); exact hupper t⟩
      have hu : raw (t,⟨0,by norm_num⟩) = p u := by
        rw [hrawcenter]
        exact p.extend_apply u.property
      have hsu : s = u := hp.injective (he.trans hu)
      have hsR : (m : ℝ)+h ≤ s := hs
      have hsuR := congrArg Subtype.val hsu
      dsimp [u] at hsuR
      have hb := mul_le_mul_of_nonneg_left t.property.2 (mul_pos hh.1 hk.1).le
      have hh' : h*k < h := by nlinarith [hh.1,hk.2]
      linarith
  let O := raw ⁻¹' Kᶜ
  have hO : IsOpen O := hK.isOpen_compl.preimage hraw.continuous
  have hbase : Set.univ ×ˢ ({⟨0,by norm_num⟩} : Set (Icc (-1 : ℝ) 1)) ⊆ O := by
    rintro ⟨t,w⟩ ⟨_,hw⟩
    have he : w = ⟨0,by norm_num⟩ := hw
    subst w
    exact havoid t
  obtain ⟨A,B,hA,hB,hUA,h0B,hAB⟩ := generalized_tube_lemma isCompact_univ isCompact_singleton hO hbase
  let clip : ℝ → Icc (-1 : ℝ) 1 := projIcc (-1) 1 (by norm_num)
  have h0pre : (0 : ℝ) ∈ clip ⁻¹' B := by
    simpa [clip,projIcc_of_mem] using h0B (Set.mem_singleton (⟨0,by norm_num⟩ : Icc (-1 : ℝ) 1))
  obtain ⟨d,hd,hdB⟩ := Metric.mem_nhds_iff.mp ((hB.preimage continuous_projIcc).mem_nhds h0pre)
  let lambda := min (d/2) (1/2 : ℝ)
  have hl : 0 < lambda ∧ lambda ≤ 1 := by
    constructor
    · dsimp [lambda]; positivity
    · have hh' := min_le_right (d/2) (1/2 : ℝ); dsimp [lambda]; linarith
  have hld : lambda < d := by have hh' := min_le_left (d/2) (1/2 : ℝ); dsimp [lambda]; linarith
  let b : D → D := fun z => (z.1,⟨lambda*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hl.1,hl.2]⟩)
  have hbc : Continuous b := by dsimp [b,D]; fun_prop
  have hbi : Function.Injective b := by
    intro z w he
    apply Prod.ext
    · simpa [b] using congrArg Prod.fst he
    · apply Subtype.ext
      exact mul_left_cancel₀ hl.1.ne' (congrArg (fun z : D => (z.2 : ℝ)) he)
  let R := raw ∘ b
  have hR : IsEmbedding R := hraw.comp ((hbc.isClosedEmbedding hbi).isEmbedding)
  have hRavoid (z : D) : R z ∉ K := by
    apply hAB ⟨hUA trivial,?_⟩
    have hw : lambda*(z.2 : ℝ) ∈ Icc (-1 : ℝ) 1 := by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hl.1,hl.2]
    have habs : |lambda*(z.2 : ℝ)| < d := by
      rw [abs_mul,abs_of_pos hl.1]
      exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hl.1.le).trans_lt (by simpa using hld)
    have hh' := hdB (show lambda*(z.2 : ℝ) ∈ Metric.ball (0 : ℝ) d by simpa [Metric.mem_ball,Real.dist_eq] using habs)
    simpa [clip,projIcc_of_mem _ hw] using hh'
  have hRcenter (t : I) : R (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+(h*k)*t) := by
    have he : b (t,⟨0,by norm_num⟩) = (t,⟨0,by norm_num⟩) := by dsimp [b]; congr 1; apply Subtype.ext; simp
    change raw (b _) = _
    rw [he,hrawcenter]
  refine ⟨lambda,hl,R,(fun z => rfl),hR,?_,?_,hRcenter,?_⟩
  · rintro q ⟨z,rfl⟩; exact Set.mem_range_self (a (b z))
  · intro w
    apply congrArg E
    apply Prod.ext
    · apply Subtype.ext; simp [a,b]
    · rfl
  · ext q
    constructor
    · rintro ⟨⟨z,rfl⟩,⟨s,hs⟩⟩
      have hsm : (m : ℝ) ≤ s := by
        as_aux_lemma =>
          by_contra hn
          have hs' : s ∈ Icc (0 : I) m := ⟨s.property.1,le_of_lt (lt_of_not_ge hn)⟩
          have hh' : R z ∈ Set.range E ∩ p '' Icc 0 m := ⟨Set.mem_range_self (a (b z)),⟨s,hs',hs⟩⟩
          rw [hpre] at hh'
          have he := hp.injective (hs.trans (Set.mem_singleton_iff.mp hh'))
          have heR := congrArg Subtype.val he
          linarith
      have hsn : (s : ℝ) < (m : ℝ)+h := by
        by_contra hn
        exact hRavoid z ⟨s,le_of_not_gt hn,hs⟩
      let t : I := ⟨((s : ℝ)-m)/h,by constructor; exact div_nonneg (sub_nonneg.mpr hsm) hh.1.le; exact (div_le_one hh.1).mpr (by linarith)⟩
      have ht : (m : ℝ)+h*t = s := by dsimp [t]; rw [mul_div_cancel₀ _ hh.1.ne']; ring
      have hEt : E (t,⟨0,by norm_num⟩) = p s := by rw [hcenter,ht,p.extend_apply s.property]
      have he := hE.injective (hEt.trans hs)
      have htv := congrArg (fun z : D => (z.1 : ℝ)) he
      change ((s : ℝ)-m)/h = k*z.1 at htv
      have hbound : (s : ℝ) ≤ (m : ℝ)+h*k := by
        have heR := (div_eq_iff hh.1.ne').mp htv
        have hmul := mul_le_mul_of_nonneg_left z.1.property.2 (mul_pos hh.1 hk.1).le
        have heprod : k*(z.1 : ℝ)*h = (h*k)*z.1 := by ring
        rw [heprod] at heR
        linarith
      exact ⟨s,⟨hsm,hbound⟩,hs⟩
    · rintro ⟨s,hs,rfl⟩
      let t : I := ⟨((s : ℝ)-m)/(h*k),by constructor; exact div_nonneg (sub_nonneg.mpr hs.1) (mul_pos hh.1 hk.1).le; exact (div_le_one (mul_pos hh.1 hk.1)).mpr (by have hsR : (s : ℝ) ≤ (m : ℝ)+h*k := hs.2; linarith)⟩
      have ht : (m : ℝ)+(h*k)*t = s := by dsimp [t]; rw [mul_div_cancel₀ _ (mul_pos hh.1 hk.1).ne']; ring
      refine ⟨⟨(t,⟨0,by norm_num⟩),?_⟩,Set.mem_range_self _⟩
      rw [hRcenter,ht,p.extend_apply s.property]

private theorem outsideBandsPackaging_3777_reverse {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (m : I) (hm0 : 0 < m) (hm1 : m < 1)
    (hmends : D.firstArc.symm '' Icc 0 m ⊆ Set.range (D.ends 0)) :
    ∃ E : I × BandWidth → S, IsEmbedding E ∧
      (∀ w, E (0,w) = D.square (squarePort D.radius D.radius_pos 0 w)) ∧
      (∀ t : I, E (t,⟨0,by norm_num⟩) = D.firstArc.symm.extend ((m : ℝ)*t)) ∧
      Set.range E ∩ Set.range D.firstArc.symm = D.firstArc.symm '' Icc 0 m ∧
      Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
      Disjoint (Set.range E) (Set.range D.secondArc) ∧
      ∃ height : I → BandWidth, Continuous height ∧ StrictMono height ∧ height 0 = ⟨0,by norm_num⟩ ∧
        ∀ z, E z = D.ends 0 (z.2,height z.1) := by
  let q := D.firstArc.symm
  have hq : IsEmbedding q := (q.continuous.isClosedEmbedding
    (D.firstArc_embedded.injective.comp unitInterval.symm_involutive.injective)).isEmbedding
  have hq_range : Set.range q = a.image \ D.openSquare := by
    rw [show Set.range q=Set.range D.firstArc from Path.symm_range _]
    exact D.firstArc_range
  have hq_square : Set.range q ∩ Set.range D.square = {q (0:I),q (1:I)} := by
    change Set.range D.firstArc.symm ∩ Set.range D.square = {D.firstArc.symm (0:I),D.firstArc.symm (1:I)}
    rw [Path.symm_range,D.firstArc_square_intersection]
    simp [Set.pair_comm]
        
  classical
  have hmR : 0 < (m : ℝ) := hm0
  let s : I → I := fun t => ⟨(m : ℝ)*t,by constructor <;> nlinarith [t.property.1,t.property.2,m.property.1,m.property.2]⟩
  have hsc : Continuous s := by dsimp [s]; fun_prop
  have hsI (t : I) : s t ∈ Icc 0 m := ⟨(s t).property.1,by change (m : ℝ)*t ≤ m; nlinarith [t.property.2]⟩
  have hs0 : s 0 = 0 := by apply Subtype.ext; simp [s]
  let A := (D.ends_embedded 0).toHomeomorph
  let u : I → Set.range (D.ends 0) := fun t => ⟨q (s t),hmends ⟨s t,hsI t,rfl⟩⟩
  have huc : Continuous u := Continuous.subtype_mk (q.continuous.comp hsc) _
  let g : I → EndRectangle := A.symm ∘ u
  have hgc : Continuous g := A.symm.continuous.comp huc
  have hforward (t : I) : D.ends 0 (g t) = q (s t) := by
    have hh := congrArg Subtype.val (A.apply_symm_apply (u t))
    exact hh
  have hgfirst (t : I) : (g t).1 = ⟨0,by norm_num⟩ := by
    apply Subtype.ext
    have haxis := (D.ends_axes 0 (g t)).1
    have hmem : q (s t) ∈ a.image := by
      have hh : q (s t) ∈ a.image \ D.openSquare := hq_range ▸ Set.mem_range_self _
      exact hh.1
    exact (haxis.mp ((hforward t).symm ▸ hmem)).2
  have hg0 : g 0 = (⟨0,by norm_num⟩,⟨0,by norm_num⟩) := by
    apply (D.ends_embedded 0).injective
    rw [hforward,hs0,q.source,D.ends_seam]
  have heighti : Function.Injective (fun t => (g t).2) := by
    as_aux_lemma =>
      intro t v he
      have he' : g t = g v := Prod.ext ((hgfirst t).trans (hgfirst v).symm) he
      have hh := congrArg (D.ends 0) he'
      rw [hforward,hforward] at hh
      have hs := hq.injective hh
      apply Subtype.ext
      have hsR := congrArg Subtype.val hs
      change (m : ℝ)*t=(m : ℝ)*v at hsR
      exact mul_left_cancel₀ hmR.ne' hsR
  let E : I × BandWidth → S := fun z => D.ends 0 (z.2,(g z.1).2)
  have hEc : Continuous E := (D.ends_embedded 0).continuous.comp (continuous_snd.prodMk ((hgc.comp continuous_fst).snd))
  have hEi : Function.Injective E := by
    intro z w he
    have hh := (D.ends_embedded 0).injective he
    apply Prod.ext
    · have hh' := congrArg Prod.snd hh
      exact heighti hh' 
    · exact congrArg Prod.fst hh
  have hE : IsEmbedding E := (hEc.isClosedEmbedding hEi).isEmbedding
  have hE0 (w : BandWidth) : E (0,w) = D.square (squarePort D.radius D.radius_pos 0 w) := by
    change D.ends 0 (w,(g 0).2) = _
    rw [hg0,D.ends_seam]
  have hEc0 (t : I) : E (t,⟨0,by norm_num⟩) = q (s t) := by
    change D.ends 0 (⟨0,by norm_num⟩,(g t).2) = _
    have he : (⟨0,by norm_num⟩,(g t).2) = g t := Prod.ext (hgfirst t).symm rfl
    exact (congrArg (D.ends 0) he).trans (hforward t)
  have hcenter (t : I) : E (t,⟨0,by norm_num⟩) = q.extend ((m : ℝ)*t) := by
    rw [hEc0]
    exact (q.extend_apply (s t).property).symm
  have hmeet : Set.range E ∩ Set.range q = q '' Icc 0 m := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨⟨z,rfl⟩,⟨v,hv⟩⟩
        have hmem : E z ∈ a.image := by
          rw [← hv]
          have hh : q v ∈ a.image \ D.openSquare := hq_range ▸ Set.mem_range_self _
          exact hh.1
        have hw : z.2 = ⟨0,by norm_num⟩ := by
          apply Subtype.ext
          exact ((D.ends_axes 0 (z.2,(g z.1).2)).1.mp hmem).2
        have he : z = (z.1,⟨0,by norm_num⟩) := Prod.ext rfl hw
        rw [he,hEc0]
        exact ⟨s z.1,hsI z.1,rfl⟩
      · rintro ⟨v,hv,rfl⟩
        let t : I := ⟨(v : ℝ)/m,⟨div_nonneg v.property.1 hmR.le,(div_le_one hmR).mpr (show (v : ℝ) ≤ m from hv.2)⟩⟩
        have ht : s t = v := by apply Subtype.ext; exact mul_div_cancel₀ _ hmR.ne'
        refine ⟨⟨(t,⟨0,by norm_num⟩),?_⟩,Set.mem_range_self _⟩
        rw [hEc0,ht]
  have hheightzero (t : I) (ht : ((g t).2 : ℝ) ≤ 0) : t = 0 := by
    as_aux_lemma =>
      have hQ : q (s t) ∈ Set.range D.square := by
        rw [← hEc0]
        exact (D.ends_square 0 (⟨0,by norm_num⟩,(g t).2)).mpr ht
      have hh : q (s t) ∈ ({q 0,q 1} : Set S) :=
        hq_square ▸ ⟨Set.mem_range_self _,hQ⟩
      rcases Set.mem_insert_iff.mp hh with he0 | he1
      · have hs := hq.injective he0
        have hsR := congrArg Subtype.val hs
        apply Subtype.ext
        change (m : ℝ)*t=0 at hsR
        exact (mul_eq_zero.mp hsR).resolve_left hmR.ne'
      · have he1' : q (s t) = q 1 := he1
        have hs := hq.injective he1'
        have hsR := congrArg Subtype.val hs
        change (m : ℝ)*t=1 at hsR
        have hb := mul_le_mul_of_nonneg_left t.property.2 m.property.1
        have hm1R : (m : ℝ)<1 := hm1
        linarith
  have hE_Q : Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨⟨z,rfl⟩,hzQ⟩
        have hz0 := hheightzero z.1 ((D.ends_square 0 (z.2,(g z.1).2)).mp hzQ)
        refine ⟨z.2,?_⟩
        have he : z = (0,z.2) := Prod.ext hz0 rfl
        rw [he,hE0]
      · rintro ⟨w,rfl⟩
        exact ⟨⟨(0,w),hE0 w⟩,Set.mem_range_self _⟩
  have hh1 : (0:ℝ) ≤ ((g (1:I)).2:ℝ) := by
    by_contra hh
    have ht := hheightzero (1:I) (le_of_lt (lt_of_not_ge hh))
    norm_num at ht
  have hle : (g (0:I)).2 ≤ (g (1:I)).2 := by
    rw [hg0]
    exact hh1
  have hmono : StrictMono (fun t => (g t).2) :=
    hgc.snd.strictMono_of_inj_boundedOrder hle heighti
  refine ⟨E,hE,hE0,hcenter,hmeet,hE_Q,?_,(fun t => (g t).2),hgc.snd,hmono,?_,?_⟩
        
  · apply Set.disjoint_left.mpr
    rintro q ⟨z,rfl⟩ hqsecond
    have hmem : E z ∈ b.image := by
      have hh : E z ∈ b.image \ D.openSquare := D.secondArc_range ▸ hqsecond
      exact hh.1
    have hh := ((D.ends_axes 0 (z.2,(g z.1).2)).2.mp hmem).1
    norm_num at hh
  · exact congrArg Prod.snd hg0
  · intro z; rfl

private theorem outsideBandsPackaging_2777_sameRange (e f : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) (hf : IsEmbedding f)
    (hag : ∀ z : ↥(Plane.closedSquare 0 1), z.val ∈ modelCurve → e z=f z) :
    Set.range e=Set.range f := by
  classical
  have hboundary (k : ↥modelCurve → Plane) (hk : IsEmbedding k) :
      IsJordanCurve (Set.range k) ∧
        ∃ F : Plane ≃ₜ Plane, ∀ z : ↥modelCurve, F z = k z := by
    as_aux_lemma =>
                    
      classical
      obtain ⟨f,hf,hfim⟩ := isJordanCurve_modelCurve
      have hfmem (t : I) : f t ∈ modelCurve := by
        rw [← hfim]
        exact ⟨t,t.property,rfl⟩
      let q : I → ↥modelCurve := fun t => ⟨f t,hfmem t⟩
      have hq : Continuous q := by
        exact (continuousOn_iff_continuous_restrict.mp hf.continuousOn).subtype_mk _
      let g : ℝ → Plane := fun t => k (q (projIcc 0 1 zero_le_one t))
      have hg : Continuous g := hk.continuous.comp
        (hq.comp continuous_projIcc)
      have hqeq (t : ℝ) (ht : t ∈ (Icc (0 : ℝ) 1)) :
          (q (projIcc 0 1 zero_le_one t) : Plane) = f t := by
        dsimp [q]
        rw [projIcc_of_mem zero_le_one ht]
      have hloop : IsLoop g := by
        as_aux_lemma =>
          refine ⟨hg.continuousOn, ?_, ?_⟩
          · apply congrArg k
            apply Subtype.ext
            rw [hqeq 0 (by norm_num),hqeq 1 (by norm_num)]
            exact hf.closes
          · intro s hs t ht he
            apply hf.injOn hs ht
            have hh := congrArg Subtype.val (hk.injective he)
            rw [hqeq s ⟨hs.1,hs.2.le⟩,hqeq t ⟨ht.1,ht.2.le⟩] at hh
            exact hh
      have him : g '' (Icc (0 : ℝ) 1) = Set.range k := by
        as_aux_lemma =>
          ext z
          constructor
          · rintro ⟨t,ht,rfl⟩
            exact Set.mem_range_self _
          · rintro ⟨v,rfl⟩
            have hvm : (v : Plane) ∈ f '' (Icc (0 : ℝ) 1) := hfim.symm ▸ v.property
            obtain ⟨t,ht,he⟩ := hvm
            refine ⟨t,ht,?_⟩
            apply congrArg k
            apply Subtype.ext
            exact (hqeq t ht).trans he
      have hJ : IsJordanCurve (Set.range k) := ⟨g,hloop,him⟩
      obtain ⟨F,hF⟩ := jordan_schoenflies_of_homeomorph
        isJordanCurve_modelCurve hJ hk.toHomeomorph
      exact ⟨hJ,F,fun z => hF z⟩
                    
  have hinterior (e : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) :
      IsPreconnected (interior (Set.range e)) ∧
        (interior (Set.range e)).Nonempty := by
    as_aux_lemma =>
                    
      let K := Plane.closedSquare 0 1
      let A : Set ↥K := {z | (z : Plane) ∈ interior K}
      have hAimage : Subtype.val '' A = interior K := by
        ext z
        constructor
        · rintro ⟨w,hw,rfl⟩; exact hw
        · intro hz; exact ⟨⟨z,interior_subset hz⟩,hz,rfl⟩
      have hAconn : IsPreconnected A := by
        apply IsInducing.subtypeVal.isPreconnected_image.mp
        rw [hAimage]
        change IsPreconnected (interior (Plane.closedSquare 0 1))
        rw [Plane.interior_closedSquare]
        exact (Plane.convex_openSquare 0 1).isPreconnected
      have heA : e '' A = interior (Set.range e) := by
        as_aux_lemma =>
          ext y
          constructor
          · rintro ⟨z,hz,rfl⟩
            exact (embedded_planar_region_interior_iff_probe K e he z).mpr hz
          · intro hy
            obtain ⟨z,rfl⟩ := interior_subset hy
            exact ⟨z,(embedded_planar_region_interior_iff_probe K e he z).mp hy,rfl⟩
      have hzero : (0 : Plane) ∈ interior K := by
        change (0 : Plane) ∈ interior (Plane.closedSquare 0 1)
        rw [Plane.interior_closedSquare]
        simp [Plane.openSquare,Plane.supNorm]
      refine ⟨heA ▸ hAconn.image e he.continuous.continuousOn, ?_⟩
      exact ⟨e ⟨0,interior_subset hzero⟩,
        (embedded_planar_region_interior_iff_probe K e he _).mpr hzero⟩
  have hside (K : Set Plane) (hK : IsCompact K)
      (hconn : IsPreconnected (interior K)) (hne : (interior K).Nonempty)
      (hJ : IsJordanCurve (frontier K)) :
      K = frontier K ∪ inside (frontier K) := by
    as_aux_lemma =>
                    
      obtain ⟨x,hx⟩ := hne
      have hsub : interior K ⊆ (frontier K)ᶜ := by
        intro z hz hzfr
        exact hzfr.2 hz
      have hfr : frontier (interior K) ∩ (frontier K)ᶜ = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro z hz
        exact hz.2 (frontier_interior_subset hz.1)
      have hcomp : connectedComponentIn (frontier K)ᶜ x = interior K :=
        Plane.connectedComponentIn_eq_of_frontier_disjoint
          isOpen_interior hconn hsub hfr hx
      have hxin : x ∈ inside (frontier K) := by
        refine ⟨hsub hx, ?_⟩
        rw [hcomp]
        exact hK.isBounded.subset interior_subset
      have hi : interior K = inside (frontier K) :=
        hcomp.symm.trans ((jordan_curve_theorem hJ).connectedComponentIn_eq_inside hxin)
      calc
        K = interior K ∪ frontier K := by
          rw [← closure_eq_interior_union_frontier, hK.isClosed.closure_eq]
        _ = frontier K ∪ inside (frontier K) := by rw [hi,union_comm]
                    
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let b : ↥modelCurve → ↥Q := fun z => ⟨z,modelCurve_subset_closedSquare z.property⟩
  have hbc : Continuous b := continuous_subtype_val.subtype_mk _
  have hbi : Function.Injective b := by
    intro z w hh
    apply Subtype.ext
    have hh' := congrArg (fun v : Q => (v : Plane)) hh
    exact hh'
  letI : CompactSpace ↥modelCurve := isCompact_iff_compactSpace.mp isJordanCurve_modelCurve.isCompact
  have hb : IsEmbedding b := (hbc.isClosedEmbedding hbi).isEmbedding
  have front (g : Q → Plane) (hg : IsEmbedding g) : Set.range (g ∘ b)=frontier (Set.range g) := by
    as_aux_lemma =>
      rw [← embedded_compact_planar_region_frontier_probe Q (isCompact_closedSquare 0 1) g hg]
      ext z
      constructor
      · rintro ⟨w,rfl⟩
        refine ⟨b w,?_,rfl⟩
        rw [← modelCurve_eq_frontier]
        exact w.property
      · rintro ⟨w,hw,rfl⟩
        have hm : (w:Plane) ∈ modelCurve := by rw [modelCurve_eq_frontier]; exact hw
        refine ⟨⟨w,hm⟩,?_⟩
        change g (b _)=g w
        congr 1
  have hfront : frontier (Set.range e)=frontier (Set.range f) := by
    rw [← front e he,← front f hf]
    have heq : e ∘ b=f ∘ b := by funext z; exact hag (b z) z.property
    rw [heq]
  have hJe : IsJordanCurve (frontier (Set.range e)) :=
    (front e he) ▸ (hboundary (e ∘ b) (he.comp hb)).1
  have hJf : IsJordanCurve (frontier (Set.range f)) := hfront ▸ hJe
  have heq := hside (Set.range e) (isCompact_range he.continuous)
    (hinterior e he).1 (hinterior e he).2 hJe
  have hfq := hside (Set.range f) (isCompact_range hf.continuous)
    (hinterior f hf).1 (hinterior f hf).2 hJf
  rw [heq,hfq,hfront]

private theorem outsideBandsPackaging_4442_narrow {S : Type} [TopologicalSpace S] [T2Space S]
    (E : I × BandWidth → S) (hE : IsEmbedding E)
    (K : Set S) (hK : IsClosed K) (c : I) (hc0 : 0<c) (hc1 : c<1)
    (δ : ℝ) (hδ : 0<δ ∧ δ≤1)
    (hcenter : ∀ t : I,t≤c → E (t,⟨0,by norm_num⟩)∉K)
    (hbottom : ∀ w : BandWidth,E (0,w)∉K)
    (hgerm : ∀ z : I × BandWidth,c≤z.1 → |(z.2:ℝ)|≤δ → (E z∈K ↔ z.1=1)) :
    ∃ scale : I → ℝ, ∃ F : I × BandWidth → S,
      Continuous scale ∧ (∀ t,0<scale t ∧ scale t≤1) ∧ scale 0=1 ∧ scale 1=δ ∧
      IsEmbedding F ∧ (∀ t,F (t,⟨0,by norm_num⟩)=E (t,⟨0,by norm_num⟩)) ∧
      (∀ w,F (0,w)=E (0,w)) ∧ Set.range F ⊆ Set.range E ∧
      (∀ z, ∃ w : BandWidth,(w:ℝ)=scale z.1*(z.2:ℝ) ∧ F z=E (z.1,w)) ∧
      (Set.range F ∩ K=Set.range (fun w : BandWidth => E (1,⟨δ*w,by
        constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩))) := by
  classical
  let O := E ⁻¹' Kᶜ
  have hO : IsOpen O := hK.isOpen_compl.preimage hE.continuous
  have hcore : (Icc (0:I) c) ×ˢ ({⟨0,by norm_num⟩} : Set BandWidth) ⊆ O := by
    rintro ⟨t,w⟩ ⟨ht,hw⟩
    have he : w=⟨0,by norm_num⟩ := mem_singleton_iff.mp hw
    subst w
    exact hcenter t ht.2
  obtain ⟨A,V,hA,hV,hTA,h0V,hAV⟩ := generalized_tube_lemma isClosed_Icc.isCompact isCompact_singleton hO hcore
  obtain ⟨d,hd,hdV⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds (h0V (mem_singleton _)))
  have hbase : ({0} : Set I) ×ˢ (univ : Set BandWidth) ⊆ O := by
    rintro ⟨t,w⟩ ⟨ht,_⟩
    have he : t=0 := mem_singleton_iff.mp ht
    subst t
    exact hbottom w
  obtain ⟨W,Q,hW,hQ,h0W,hUQ,hWQ⟩ := generalized_tube_lemma isCompact_singleton isCompact_univ hO hbase
  obtain ⟨b,hb,hbW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds (h0W (mem_singleton _)))
  let a : ℝ := min b ((c:ℝ)/2)
  have ha : 0<a := lt_min hb (half_pos (show 0<(c:ℝ) from hc0))
  have hab : a≤b := min_le_left _ _
  have hac : a<(c:ℝ) := by have := min_le_right b ((c:ℝ)/2); dsimp [a]; linarith
  let ε : ℝ := min (d/2) δ
  have hε : 0<ε := lt_min (half_pos hd) hδ.1
  have hεδ : ε≤δ := min_le_right _ _
  have hε1 : ε≤1 := hεδ.trans hδ.2
  have hεd : ε<d := by have := min_le_left (d/2) δ; dsimp [ε]; linarith
  let scale : I → ℝ := fun t => max ε (max (1-(t:ℝ)/a) (δ*max 0 (((t:ℝ)-c)/(1-(c:ℝ)))))
  have hsC : Continuous scale := by dsimp [scale]; fun_prop
  have hden : 0<1-(c:ℝ) := sub_pos.mpr hc1
  have hs (t : I) : 0<scale t ∧ scale t≤1 := by
    as_aux_lemma =>
      constructor
      · exact lt_of_lt_of_le hε (le_max_left _ _)
      · apply max_le hε1
        apply max_le
        · have := div_nonneg t.property.1 ha.le
          linarith
        · have hh : max 0 (((t:ℝ)-c)/(1-(c:ℝ)))≤1 := by
            apply max_le (by norm_num)
            exact (div_le_one hden).mpr (by linarith [t.property.2])
          exact (mul_le_mul_of_nonneg_left hh hδ.1.le).trans (by simpa using hδ.2)
  have hs0 : scale 0=1 := by
    have hneg : (-(c:ℝ))/(1-(c:ℝ))≤0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    simp [scale,max_eq_left hneg,max_eq_right hε1]
  have hs1 : scale 1=δ := by
    as_aux_lemma =>
      have hsmall : 1-1/a≤δ := by
        have ha1 : a<1 := hac.trans hc1
        have hinv : 1≤1/a := (one_le_div ha).mpr ha1.le
        linarith [hδ.1]
      change max ε (max (1-1/a) (δ*max 0 ((1-(c:ℝ))/(1-(c:ℝ)))))=δ
      rw [div_self hden.ne']
      rw [max_eq_right (by norm_num : (0:ℝ)≤1)]
      rw [mul_one,max_eq_right hsmall,max_eq_right hεδ]
  let k : I × BandWidth → I × BandWidth := fun z =>
    (z.1,⟨scale z.1*(z.2:ℝ),by
      have hst := hs z.1
      constructor <;> nlinarith [z.2.property.1,z.2.property.2]⟩)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    as_aux_lemma =>
      intro z w he
      have ht : z.1=w.1 := by simpa [k] using congrArg Prod.fst he
      apply Prod.ext ht
      apply Subtype.ext
      have hw := congrArg (fun q : I × BandWidth => (q.2:ℝ)) he
      change scale z.1*(z.2:ℝ)=scale w.1*(w.2:ℝ) at hw
      rw [←ht] at hw
      exact mul_left_cancel₀ (hs z.1).1.ne' hw
  let F := E ∘ k
  have hFc : Continuous F := hE.continuous.comp hkc
  have hFi : Function.Injective F := hE.injective.comp hki
  have hk1 (w : BandWidth) : k (1,w)=(1,⟨δ*w,by constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩) := by
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change scale 1*w=δ*w
    rw [hs1]
  have hmeet (z : I × BandWidth) : F z∈K ↔ z.1=1 := by
    as_aux_lemma =>
      by_cases ht : c≤z.1
      · have haT : a≤(z.1:ℝ) := hac.le.trans ht
        have hbase0 : 1-(z.1:ℝ)/a≤0 := by have := (one_le_div ha).mpr haT; linarith
        have hramp : δ*max 0 (((z.1:ℝ)-c)/(1-(c:ℝ)))≤δ := by
          apply (mul_le_mul_of_nonneg_left (show max 0 (((z.1:ℝ)-c)/(1-(c:ℝ)))≤1 from max_le (by norm_num) ((div_le_one hden).mpr (by linarith [z.1.property.2]))) hδ.1.le).trans
          simp
        have hsδ : scale z.1≤δ := max_le hεδ (max_le (hbase0.trans hδ.1.le) hramp)
        have hw : |((k z).2:ℝ)|≤δ := by
          change |scale z.1*(z.2:ℝ)|≤δ
          rw [abs_mul,abs_of_pos (hs z.1).1]
          exact (mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) (hs z.1).1.le).trans (by simpa using hsδ)
        exact hgerm (k z) ht hw
      · have htc : z.1≤c := le_of_not_ge ht
        have hz0 : z.1≠1 := by intro he; rw [he] at ht; exact ht c.property.2
        have hnot : F z∉K := by
          as_aux_lemma =>
            by_cases hsmall : (z.1:ℝ)<a
            · have htW : z.1∈W := by
                apply hbW
                change dist z.1 (0:I)<b
                rw [Subtype.dist_eq,Real.dist_eq]
                change |(z.1:ℝ)-0|<b
                rw [sub_zero,abs_of_nonneg z.1.property.1]
                exact hsmall.trans_le hab
              have ho : k z∈O := hWQ ⟨htW,hUQ (mem_univ _)⟩
              exact ho
            · have hbase0 : 1-(z.1:ℝ)/a≤0 := by have := (one_le_div ha).mpr (le_of_not_gt hsmall); linarith
              have hramp0 : ((z.1:ℝ)-c)/(1-(c:ℝ))≤0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr htc) hden.le
              have hseq : scale z.1=ε := by
                change max ε (max (1-(z.1:ℝ)/a) (δ*max 0 (((z.1:ℝ)-c)/(1-(c:ℝ)))))=ε
                rw [max_eq_left hramp0,mul_zero,max_eq_right hbase0,max_eq_left hε.le]
              have hwV : (k z).2∈V := by
                apply hdV
                change dist (k z).2 (⟨0,by norm_num⟩ : BandWidth)<d
                rw [Subtype.dist_eq,Real.dist_eq,sub_zero]
                change |scale z.1*(z.2:ℝ)|<d
                rw [hseq,abs_mul,abs_of_pos hε]
                exact lt_of_le_of_lt ((mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hε.le).trans (by simp)) hεd
              have ho : k z∈O := hAV ⟨hTA ⟨z.1.property.1,htc⟩,hwV⟩
              exact ho
        exact iff_of_false hnot hz0
  refine ⟨scale,F,hsC,hs,hs0,hs1,(hFc.isClosedEmbedding hFi).isEmbedding,?_,?_,?_,?_,?_⟩
  · intro t
    change E (k (t,⟨0,by norm_num⟩))=E (t,⟨0,by norm_num⟩)
    congr 1
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    simp [k]
  · intro w
    change E (k (0,w))=E (0,w)
    congr 1
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    change scale 0*w=w
    simp [hs0]
  · rintro x ⟨z,rfl⟩
    exact Set.mem_range_self (k z)
  · intro z
    exact ⟨(k z).2,rfl,rfl⟩
  · ext x
    constructor
    · rintro ⟨⟨z,rfl⟩,hz⟩
      have ht := (hmeet z).mp hz
      refine ⟨z.2,?_⟩
      change E _=E (k z)
      rw [show z=(1,z.2) from Prod.ext ht rfl,hk1]
    · rintro ⟨w,rfl⟩
      have he : F (1,w)=E (1,⟨δ*w,by constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩) := congrArg E (hk1 w)
      refine ⟨⟨(1,w),he⟩,?_⟩
      change E _∈K
      rw [←he]
      exact (hmeet (1,w)).mpr rfl

private theorem outsideBandsPackaging_554_whole_future {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m n : I) (hmn : m < n)
    (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
    (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
    (B : I × Icc (-1 : ℝ) 1 → S)
    (hBE : Set.range B ⊆ Set.range E)
    (e : OpenPartialHomeomorph S Plane) (hBs : Set.range B ⊆ e.source)
    (hport : B (1,⟨0,by norm_num⟩) = p m)
    (hps : p '' Icc m n ⊆ e.source)
    (H : Plane ≃ₜ Plane)
    (hH : ∀ z : I × Icc (-1 : ℝ) 1, H (Plane.mk (-1+2*z.1) z.2) = e (B z))
    (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hmV : p m ∈ V)
    (hpU : p '' Icc m n ⊆ U)
    (hEV : Set.range E ∩ V ⊆ Set.range B) :
    ∃ rho : ℝ, ∃ hrho : 0 < rho ∧ rho ≤ 1,
      ∃ P : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding P ∧ Set.range P ⊆ U ∧
        (∀ w : Icc (-1 : ℝ) 1, P (0,w) = B (1,⟨rho*w,by constructor <;> nlinarith [w.property.1,w.property.2,hrho.1,hrho.2]⟩)) ∧
        (∀ t : I, P (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+((n : ℝ)-m)*t)) ∧
        Set.range P ∩ Set.range E = Set.range (fun w : Icc (-1 : ℝ) 1 => P (0,w)) := by
  have normalize
      {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m n : I) (hmn : m < n)
      (E : I × Icc (-1 : ℝ) 1 → S)
      (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
      (B : I × Icc (-1 : ℝ) 1 → S)
      (hBE : Set.range B ⊆ Set.range E)
      (e : OpenPartialHomeomorph S Plane) (hBs : Set.range B ⊆ e.source)
      (hport : B (1,⟨0,by norm_num⟩) = p m)
      (hps : p '' Icc m n ⊆ e.source)
      (H : Plane ≃ₜ Plane)
      (hH : ∀ z : I × Icc (-1 : ℝ) 1, H (Plane.mk (-1+2*z.1) z.2) = e (B z)) :
      ∃ z : Plane, ∃ q : Path (Plane.mk 1 0) z,
        IsEmbedding q ∧ Set.range q ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0} ∧
        ∀ t : I, q t = H.symm (e (p.extend ((m : ℝ)+((n : ℝ)-m)*t))) := by
    as_aux_lemma =>
      let s : I → I := fun t => ⟨(m : ℝ)+((n : ℝ)-m)*t,by
        constructor
        · exact add_nonneg m.property.1 (mul_nonneg (sub_pos.mpr (show (m : ℝ)<n from hmn)).le t.property.1)
        · have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith [n.property.2]⟩
      have hsc : Continuous s := by dsimp [s]; fun_prop
      have hsi : Function.Injective s := by
        intro t u he
        apply Subtype.ext
        have hh := congrArg Subtype.val he
        change (m : ℝ)+((n : ℝ)-m)*t=(m : ℝ)+((n : ℝ)-m)*u at hh
        nlinarith [show (m : ℝ)<n from hmn]
      have hs0 : s 0 = m := by apply Subtype.ext; simp [s]
      have hs1 : s 1 = n := by apply Subtype.ext; dsimp [s]; ring
      have hsI (t : I) : s t ∈ Icc m n := by
        constructor
        · change (m : ℝ) ≤ (m : ℝ)+((n : ℝ)-m)*t
          nlinarith [t.property.1,show (m : ℝ)<n from hmn]
        · change (m : ℝ)+((n : ℝ)-m)*t ≤ n
          have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith
      let raw : I → Plane := H.symm ∘ e ∘ p ∘ s
      have hrawc : Continuous raw := by
        apply H.symm.continuous.comp
        apply e.continuousOn.comp_continuous (hp.continuous.comp hsc)
        intro t
        exact hps ⟨s t,hsI t,rfl⟩
      have hrawi : Function.Injective raw := by
        intro t u he
        apply hsi
        apply hp.injective
        apply e.injOn (hps ⟨s t,hsI t,rfl⟩) (hps ⟨s u,hsI u,rfl⟩)
        exact H.symm.injective he
      have hHp : H (Plane.mk 1 0) = e (p m) := by
        have hh := (hH (1,⟨0,by norm_num⟩)).trans (congrArg e hport)
        norm_num at hh ⊢
        exact hh
      have hraw0 : raw 0 = Plane.mk 1 0 := by
        change H.symm (e (p (s 0))) = _
        rw [hs0,← hHp,H.symm_apply_apply]
      let q : Path (Plane.mk 1 0) (raw 1) := {toFun := raw,continuous_toFun := hrawc,source' := hraw0,target' := rfl}
      have hq : IsEmbedding q := (hrawc.isClosedEmbedding hrawi).isEmbedding
      have hqQ : Set.range q ∩ Plane.closedSquare 0 1 = {Plane.mk 1 0} := by
        as_aux_lemma =>
          ext v
          constructor
          · rintro ⟨⟨t,rfl⟩,hv⟩
            have hvn := mem_closedSquare_zero_one.mp hv
            have hvx := abs_le.mp ((Plane.abs_zero_le_supNorm (q t)).trans hvn)
            have hvy := abs_le.mp ((Plane.abs_one_le_supNorm (q t)).trans hvn)
            let a : I × Icc (-1 : ℝ) 1 := (⟨(q t 0+1)/2,by constructor <;> linarith [hvx.1,hvx.2]⟩,⟨q t 1,hvy⟩)
            have hcoord : Plane.mk (-1+2*(a.1 : ℝ)) a.2 = q t := by
              ext i
              fin_cases i
              · dsimp [a,Plane.mk]; ring
              · rfl
            have he : e (B a) = e (p (s t)) := by
              rw [← hH,hcoord]
              change H (H.symm (e (p (s t)))) = _
              exact H.apply_symm_apply _
            have hEq : B a = p (s t) := e.injOn (hBs (Set.mem_range_self _)) (hps ⟨s t,hsI t,rfl⟩) he
            have hmem : p (s t) ∈ Set.range E ∩ Set.range p :=
              ⟨hBE ⟨a,hEq⟩,Set.mem_range_self _⟩
            obtain ⟨u,hu,huEq⟩ := hmeet ▸ hmem
            have hus : u = s t := hp.injective huEq
            have huR : (s t : ℝ) ≤ m := by change s t ≤ m; rw [← hus]; exact hu.2
            have htR : (t : ℝ) = 0 := by
              change (m : ℝ)+((n : ℝ)-m)*t ≤ m at huR
              nlinarith [t.property.1,show (m : ℝ)<n from hmn]
            have ht : t = 0 := Subtype.ext htR
            rw [ht,q.source]
            exact Set.mem_singleton _
          · intro hv
            have he : v = Plane.mk 1 0 := hv
            rw [he]
            refine ⟨⟨0,q.source⟩,?_⟩
            rw [mem_closedSquare_zero_one]
            norm_num [Plane.supNorm,Plane.mk]
      refine ⟨raw 1,q,hq,hqQ,?_⟩
      intro t
      change H.symm (e (p (s t))) = _
      rw [p.extend_apply (s t).property]
  classical
  obtain ⟨z,q,hq,hqQ,hparam⟩ := normalize p hp m n hmn E hmeet B hBE e hBs hport hps H hH
  let W : Set S := U ∩ (V ∪ (Set.range E)ᶜ)
  have hW : IsOpen W := hU.inter (hV.union (isCompact_range hE.continuous).isClosed.isOpen_compl)
  have hpsW : p '' Icc m n ⊆ W := by
    as_aux_lemma =>
      rintro a ⟨s,hs,rfl⟩
      refine ⟨hpU ⟨s,hs,rfl⟩,?_⟩
      by_cases he : s = m
      · exact Or.inl (he ▸ hmV)
      · right
        intro hpE
        have hmem : p s ∈ Set.range E ∩ Set.range p := ⟨hpE,Set.mem_range_self _⟩
        obtain ⟨t,ht,htEq⟩ := hmeet ▸ hmem
        have hts : t = s := hp.injective htEq
        apply he
        apply le_antisymm
        · rw [← hts]; exact ht.2
        · exact hs.1
  let O : Set Plane := H ⁻¹' (e.target ∩ e.symm ⁻¹' W)
  have hO : IsOpen O := (e.symm.isOpen_inter_preimage hW).preimage H.continuous
  have hqO : Set.range q ⊆ O := by
    as_aux_lemma =>
      rintro v ⟨t,rfl⟩
      let s : I := ⟨(m : ℝ)+((n : ℝ)-m)*t,by
        constructor
        · exact add_nonneg m.property.1 (mul_nonneg (sub_pos.mpr (show (m : ℝ)<n from hmn)).le t.property.1)
        · have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith [n.property.2]⟩
      have hs : s ∈ Icc m n := by
        constructor
        · change (m : ℝ) ≤ (m : ℝ)+((n : ℝ)-m)*t
          nlinarith [t.property.1,show (m : ℝ)<n from hmn]
        · change (m : ℝ)+((n : ℝ)-m)*t ≤ n
          have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith
      have hparam' : q t = H.symm (e (p s)) := by rw [hparam,p.extend_apply s.property]
      have hsource : p s ∈ e.source := hps ⟨s,hs,rfl⟩
      change H (q t) ∈ e.target ∩ e.symm ⁻¹' W
      rw [hparam',H.apply_symm_apply]
      exact ⟨e.map_source hsource,by change e.symm (e (p s)) ∈ W; rw [e.left_inv hsource]; exact hpsW ⟨s,hs,rfl⟩⟩
  obtain ⟨rho,hr0,hr1,C,hC,hC0,hCc,hCO,hCQ⟩ := actual_whole_exterior_whisker_half_collar q hq hqQ O hO hqO
  have hrho : 0 < rho ∧ rho ≤ 1 := ⟨hr0,hr1⟩
  let D := I × Icc (-1 : ℝ) 1
  let P : D → S := e.symm ∘ H ∘ C
  have htarget (z : D) : H (C z) ∈ e.target := (hCO (Set.mem_range_self z)).1
  have hPc : Continuous P := e.symm.continuousOn.comp_continuous (H.continuous.comp hC.continuous) htarget
  have hPi : Function.Injective P := by
    intro a b he
    apply hC.injective
    apply H.injective
    exact e.symm.injOn (htarget a) (htarget b) he
  have hP : IsEmbedding P := (hPc.isClosedEmbedding hPi).isEmbedding
  have hPW (z : D) : P z ∈ W := (hCO (Set.mem_range_self z)).2
  have hforward (z : D) : e (P z) = H (C z) := e.right_inv (htarget z)
  have hP0 (w : Icc (-1 : ℝ) 1) : P (0,w) = B (1,⟨rho*w,by constructor <;> nlinarith [w.property.1,w.property.2,hr0,hr1]⟩) := by
    have hh := hH (1,⟨rho*w,by constructor <;> nlinarith [w.property.1,w.property.2,hr0,hr1]⟩)
    norm_num at hh
    change e.symm (H (C (0,w))) = _
    rw [hC0,hh,e.left_inv (hBs (Set.mem_range_self _))]
  have hPcenter (t : I) : P (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+((n : ℝ)-m)*t) := by
    as_aux_lemma =>
      let s : I := ⟨(m : ℝ)+((n : ℝ)-m)*t,by
        constructor
        · exact add_nonneg m.property.1 (mul_nonneg (sub_pos.mpr (show (m : ℝ)<n from hmn)).le t.property.1)
        · have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith [n.property.2]⟩
      have hs : s ∈ Icc m n := by
        constructor
        · change (m : ℝ) ≤ (m : ℝ)+((n : ℝ)-m)*t
          nlinarith [t.property.1,show (m : ℝ)<n from hmn]
        · change (m : ℝ)+((n : ℝ)-m)*t ≤ n
          have hb := mul_le_mul_of_nonneg_left t.property.2 (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith
      change e.symm (H (C (t,⟨0,by norm_num⟩))) = _
      rw [hCc,hparam,p.extend_apply s.property,H.apply_symm_apply,e.left_inv (hps ⟨s,hs,rfl⟩)]
  refine ⟨rho,hrho,P,hP,?_,hP0,hPcenter,?_⟩
  · rintro v ⟨z,rfl⟩; exact (hPW z).1
  · ext v
    constructor
    · rintro ⟨⟨z,rfl⟩,hzE⟩
      have hzB : P z ∈ Set.range B := by
        rcases (hPW z).2 with hzV | hznot
        · exact hEV ⟨hzE,hzV⟩
        · exact False.elim (hznot hzE)
      obtain ⟨b,hb⟩ := hzB
      have he : C z = Plane.mk (-1+2*b.1) b.2 := by
        apply H.injective
        rw [← hforward,← hb,← hH]
      have hnorm : Plane.mk (-1+2*b.1) b.2 ∈ Plane.closedSquare 0 1 := by
        rw [mem_closedSquare_zero_one]
        change max |(-1+2*(b.1 : ℝ))| |(b.2 : ℝ)| ≤ 1
        exact max_le (abs_le.mpr ⟨by linarith [b.1.property.1],by linarith [b.1.property.2]⟩) (abs_le.mpr b.2.property)
      have hmem : C z ∈ Set.range C ∩ Plane.closedSquare 0 1 := ⟨Set.mem_range_self _,he.symm ▸ hnorm⟩
      obtain ⟨w,_,hw⟩ := hCQ ▸ hmem
      have he' : C (0,w) = C z := (hC0 w).trans hw
      have hzw : (0,w) = z := hC.injective he'
      exact ⟨w,congrArg P hzw⟩
    · rintro ⟨w,rfl⟩
      exact ⟨Set.mem_range_self _,hBE ⟨_,(hP0 w).symm⟩⟩

private theorem outsideBandsPackaging_3262_surface {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (center span : ℝ) (hspan : span ≠ 0)
    (hwindow : ∀ x : ℝ, |x| ≤ 2 → 0 < center+span*x ∧ center+span*x < 1)
    (H : Plane ≃ₜ Plane)
    (hfix : ∀ z, z ∉ Plane.openSquare 0 2 → H z=z)
    (haxis : ∀ t : ℝ,H (Plane.mk t 0)=Plane.mk t 0) :
    ∃ E : ↥(Plane.closedSquare 0 1) → S, IsEmbedding E ∧
      Set.range E ⊆ Set.range (D.ends 0) ∧
      Disjoint (Set.range E) (Set.range D.square) ∧
      (∀ z, ∃ v : EndRectangle, D.ends 0 v=E z ∧
        (v.1:ℝ)=(z.val 1)/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0)) ∧
      ∃ F : S ≃ₜ S,
        (∀ x, x ∉ Set.range (D.ends 0) → F x=x) ∧
        (∀ x, x ∈ a.image → F x=x) ∧
        (∀ x, x ∈ b.image → F x=x) ∧
        (∀ x, x ∈ Set.range D.square → F x=x) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),
          ∃ w : ↥(Plane.closedSquare 0 1),
            w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w := by
  have lift {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      (E : ↥(Plane.closedSquare 0 1) → S) (hE : IsEmbedding E)
      (H : Plane ≃ₜ Plane)
      (hfix : ∀ z, z ∉ Plane.openSquare 0 1 → H z=z) :
      ∃ F : S ≃ₜ S,
        (∀ z : ↥(Plane.closedSquare 0 1), F (E z)=E ⟨H z,by
          by_contra hh
          have ho : H z ∉ Plane.openSquare 0 1 := fun hz => hh ((Plane.openSquare_subset_closedSquare 0 1) hz)
          have he : H (H z)=H z := hfix _ ho
          have he' : H z=z := H.injective he
          exact hh (he'.symm ▸ z.property)⟩) ∧
        (∀ x, x ∉ interior (Set.range E) → F x=x) := by
    apply outsideBandsPackaging_3282_lift <;> assumption
  let Q := Plane.closedSquare 0 1
  let : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let scale : Plane ≃ₜ Plane := {
    toFun := fun z => (2:ℝ) • z
    invFun := fun z => (1/2:ℝ) • z
    left_inv := by intro z; ext i; simp
    right_inv := by intro z; ext i; simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let K := scale.trans (H.trans scale.symm)
  have hKfix (z : Plane) (hz : z ∉ Plane.openSquare 0 1) : K z=z := by
    as_aux_lemma =>
      have hz' : (2:ℝ) • z ∉ Plane.openSquare 0 2 := by
        as_aux_lemma =>
          intro hh
          apply hz
          have hh' : max |(2:ℝ)*z 0| |(2:ℝ)*z 1| < 2 := by
            simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hh
          have h0 := (max_lt_iff.mp hh').1
          have h1 := (max_lt_iff.mp hh').2
          have h0' : |z 0|<1 := by rw [abs_mul] at h0; norm_num at h0; linarith
          have h1' : |z 1|<1 := by rw [abs_mul] at h1; norm_num at h1; linarith
          simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using max_lt h0' h1'
      change (1/2:ℝ) • H ((2:ℝ) • z)=z
      rw [hfix _ hz']
      ext i
      simp
  have hKaxis (t : ℝ) : K (Plane.mk t 0)=Plane.mk t 0 := by
    have hscaled : (2:ℝ) • Plane.mk t 0 = Plane.mk (2*t) 0 := by ext i; fin_cases i <;> simp [Plane.mk]
    change (1/2:ℝ) • H ((2:ℝ) • Plane.mk t 0)=Plane.mk t 0
    rw [hscaled,haxis]
    ext i
    fin_cases i <;> simp [Plane.mk]
  let j : Q → EndRectangle := fun z =>
    (⟨z.val 1/2,by
      have hy : |z.val 1| ≤ 1 := (le_max_right _ _).trans
        (show max |z.val 0| |z.val 1|≤1 from by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
      constructor <;> linarith [(abs_le.mp hy).1,(abs_le.mp hy).2]⟩,
     ⟨center+span*(2*z.val 0),by
      have hx : |2*z.val 0|≤2 := by
        have hx : |z.val 0| ≤ 1 := (le_max_left _ _).trans
          (show max |z.val 0| |z.val 1|≤1 from by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
        rw [abs_mul]; norm_num; linarith
      have hw := hwindow _ hx
      exact ⟨by linarith,hw.2.le⟩⟩)
  have hjc : Continuous j := by dsimp [j]; fun_prop
  have hji : Function.Injective j := by
    as_aux_lemma =>
      intro z w he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · have hh := congrArg (fun q : EndRectangle => (q.2:ℝ)) he
        change center+span*(2*z.val 0)=center+span*(2*w.val 0) at hh
        have hh' : span*(2*z.val 0)=span*(2*w.val 0) := by linarith
        have hh'' := mul_left_cancel₀ hspan hh'
        change z.val 0 = w.val 0
        linarith
      · have hh := congrArg (fun q : EndRectangle => (q.1:ℝ)) he
        change z.val 1/2=w.val 1/2 at hh
        change z.val 1 = w.val 1
        linarith
  let E := D.ends 0 ∘ j
  have hE : IsEmbedding E := (D.ends_embedded 0).comp
    (hjc.isClosedEmbedding hji).isEmbedding
  have hEs : Set.range E ⊆ Set.range (D.ends 0) := by
    rintro x ⟨z,rfl⟩; exact Set.mem_range_self (j z)
  have hEq : Disjoint (Set.range E) (Set.range D.square) := by
    as_aux_lemma =>
      apply Set.disjoint_left.mpr
      rintro x ⟨z,rfl⟩ hQ
      have hh := (D.ends_square 0 (j z)).mp hQ
      have hx : |2*z.val 0|≤2 := by
        have hz : max |z.val 0| |z.val 1|≤1 := by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
        have hx := (le_max_left _ _).trans hz
        rw [abs_mul]; norm_num; linarith
      exact (not_le_of_gt (hwindow _ hx).1) hh
  obtain ⟨F,hFE,hFfix⟩ := lift E hE K hKfix
  have houtside (x : S) (hx : x ∉ Set.range E) : F x=x :=
    hFfix x (fun h => hx (interior_subset h))
  have hFa (x : S) (hx : x ∈ a.image) : F x=x := by
    as_aux_lemma =>
      by_cases hmem : x ∈ Set.range E
      · obtain ⟨z,rfl⟩ := hmem
        have hh := ((D.ends_axes 0 (j z)).1.mp hx).2
        have hz : z.val 1=0 := by change z.val 1/2=0 at hh; linarith
        have hpoint : z.val=Plane.mk (z.val 0) 0 := by ext i; fin_cases i <;> simp [hz]
        have hKz : K z.val=z.val := by rw [hpoint,hKaxis]
        rw [hFE]
        congr 1
        exact Subtype.ext hKz
      · exact houtside x hmem
  refine ⟨E,hE,hEs,hEq,(fun z => ⟨j z,rfl,rfl,rfl⟩),F,?_,hFa,?_,?_,?_⟩
  · intro x hx
    exact houtside x (fun h => hx (hEs h))
  · intro x hx
    apply houtside
    rintro ⟨z,rfl⟩
    have hh := ((D.ends_axes 0 (j z)).2.mp hx).1
    norm_num at hh
  · intro x hx
    exact houtside x (fun he => Set.disjoint_left.mp hEq he hx)
  · intro z
    refine ⟨⟨K z,by
      by_contra hh
      have ho : K z ∉ Plane.openSquare 0 1 := fun hz => hh ((Plane.openSquare_subset_closedSquare 0 1) hz)
      have he : K (K z)=K z := hKfix _ ho
      have he' : K z=z := K.injective he
      exact hh (he'.symm ▸ z.property)⟩,rfl,hFE z⟩

private theorem outsideBandsPackaging_4420_narrow {S : Type} [TopologicalSpace S] [T2Space S]
    (G R : I × BandWidth → S) (hG : IsEmbedding G) (hR : IsEmbedding R)
    (τ c : I) (hτ : 0<τ) (hc : 0<c ∧ c<1)
    (η : ℝ) (hη : 0<η ∧ η≤1)
    (hseam : ∀ w,R (0,w)=G (τ,⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩))
    (hcore : ∀ t : I,t<1 → G
      (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
       ⟨0,by norm_num⟩)∉Set.range R)
    (hbottom : ∀ w,G (0,w)∉Set.range R)
    (hgerm : ∀ t : I,c≤t → ∀ w : BandWidth,
      G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
         ⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)∈Set.range R ↔ t=1) :
    ∃ L : I × BandWidth → S,IsEmbedding L ∧
      (∀ w,L (0,w)=G (0,w)) ∧ (∀ w,L (1,w)=R (0,w)) ∧
      (∀ t : I,L (t,⟨0,by norm_num⟩)=G
        (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
         ⟨0,by norm_num⟩)) ∧
      Set.range L ⊆ Set.range G ∧
      Set.range L ∩ Set.range R=Set.range (fun w => R (0,w)) ∧
      ∃ scale : I → ℝ,Continuous scale ∧ (∀ t,0<scale t ∧ scale t≤1) ∧
        ∀ z,∃ t : I,∃ w : BandWidth,(t:ℝ)=(τ:ℝ)*z.1 ∧
          (w:ℝ)=scale z.1*z.2 ∧ L z=G (t,w) := by
  have narrow {S : Type} [TopologicalSpace S] [T2Space S]
      (E : I × BandWidth → S) (hE : IsEmbedding E)
      (K : Set S) (hK : IsClosed K) (c : I) (hc0 : 0<c) (hc1 : c<1)
      (δ : ℝ) (hδ : 0<δ ∧ δ≤1)
      (hcenter : ∀ t : I,t≤c → E (t,⟨0,by norm_num⟩)∉K)
      (hbottom : ∀ w : BandWidth,E (0,w)∉K)
      (hgerm : ∀ z : I × BandWidth,c≤z.1 → |(z.2:ℝ)|≤δ → (E z∈K ↔ z.1=1)) :
      ∃ scale : I → ℝ, ∃ F : I × BandWidth → S,
        Continuous scale ∧ (∀ t,0<scale t ∧ scale t≤1) ∧ scale 0=1 ∧ scale 1=δ ∧
        IsEmbedding F ∧ (∀ t,F (t,⟨0,by norm_num⟩)=E (t,⟨0,by norm_num⟩)) ∧
        (∀ w,F (0,w)=E (0,w)) ∧ Set.range F ⊆ Set.range E ∧
        (∀ z, ∃ w : BandWidth,(w:ℝ)=scale z.1*(z.2:ℝ) ∧ F z=E (z.1,w)) ∧
        (Set.range F ∩ K=Set.range (fun w : BandWidth => E (1,⟨δ*w,by
          constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩))) := by
    apply outsideBandsPackaging_4442_narrow <;> assumption
  let k : I × BandWidth → I × BandWidth := fun z =>
    (⟨(τ:ℝ)*z.1,by constructor <;> nlinarith [τ.property.1,τ.property.2,z.1.property.1,z.1.property.2]⟩,z.2)
  have hkc : Continuous k := by dsimp [k]; fun_prop
  have hki : Function.Injective k := by
    intro z w he
    have hh0 := congrArg (fun q : I × BandWidth => (q.1:ℝ)) he
    have he0 : z.1=w.1 := Subtype.ext (mul_left_cancel₀ (show (τ:ℝ)≠0 from ne_of_gt (show 0<(τ:ℝ) from hτ)) hh0)
    apply Prod.ext he0
    have hh1 : z.2=w.2 := Prod.mk.inj he |>.2
    exact hh1
  let B := G ∘ k
  have hB : IsEmbedding B := hG.comp (hkc.isClosedEmbedding hki).isEmbedding
  have hBm (z : I × BandWidth) (ht : c≤z.1) (hw : |(z.2:ℝ)|≤η) :
      B z∈Set.range R ↔ z.1=1 := by
    as_aux_lemma =>
      let w : BandWidth := ⟨(z.2:ℝ)/η,by
        have hh := abs_le.mp hw
        constructor
        · apply (le_div_iff₀ hη.1).mpr
          nlinarith [hh.1]
        · apply (div_le_iff₀ hη.1).mpr
          nlinarith [hh.2]⟩
      have hew : η*(w:ℝ)=(z.2:ℝ) := by dsimp [w]; field_simp [hη.1.ne']
      have he : B z=G
        (⟨(τ:ℝ)*z.1,by constructor <;> nlinarith [τ.property.1,τ.property.2,z.1.property.1,z.1.property.2]⟩,
         ⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩) := by
        change G (k z)=_
        apply congrArg G
        apply Prod.ext
        · rfl
        · exact Subtype.ext hew.symm
      rw [he]
      exact hgerm z.1 ht w
  have hBb (w : BandWidth) : B (0,w)∉Set.range R := by
    change G (⟨(τ:ℝ)*(0:I),_⟩,w)∉Set.range R
    simpa using hbottom w
  obtain ⟨scale,L,hsc,hs,hsc0,hsc1,hL,hLc,hL0,hLs,hwidth,hLmeet⟩ :=
    narrow B hB (Set.range R) (isCompact_range hR.continuous).isClosed c hc.1 hc.2 η hη
      (fun t ht => hcore t (ht.trans_lt hc.2)) hBb hBm
  have hL1 (w : BandWidth) : L (1,w)=R (0,w) := by
    as_aux_lemma =>
      obtain ⟨v,hv,hLv⟩ := hwidth (1,w)
      have hv' : (v:ℝ)=η*w := by simpa [hsc1] using hv
      rw [hLv]
      change G (⟨(τ:ℝ)*(1:I),_⟩,v)=R (0,w)
      have ht : (⟨(τ:ℝ)*(1:I),by simpa using τ.property⟩ : I)=τ := by apply Subtype.ext; simp
      rw [ht]
      exact (congrArg (fun v : BandWidth => G (τ,v)) (Subtype.ext hv')).trans (hseam w).symm
  refine ⟨L,hL,?_,hL1,hLc,?_,?_,scale,hsc,hs,?_⟩
  · intro w
    simpa [B,k] using hL0 w
  · intro x hx
    obtain ⟨z,rfl⟩ := hLs hx
    exact Set.mem_range_self (k z)
  · rw [hLmeet]
    congr 1
    funext w
    have htop : L (1,w)=B (1,⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩) := by
      obtain ⟨v,hv,hLv⟩ := hwidth (1,w)
      rw [hLv]
      have hv' : v=⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩ :=
        Subtype.ext (by simpa [hsc1] using hv)
      rw [hv']
    exact htop.symm.trans (hL1 w)
  · intro z
    obtain ⟨w,hw,hLw⟩ := hwidth z
    exact ⟨(k (z.1,w)).1,w,rfl,hw,hLw⟩

private theorem outsideBandsPackaging_2527_boundary (R : ℝ) (hR : 1<R)
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hBU : Set.range B ⊆ Plane.openSquare 0 R)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
    ∃ F : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 R → F z=z) ∧
      (∀ z, z 1≤0 → F z=z) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        z.val ∈ modelCurve → 0≤z.val 1 → F z = B z := by
  have upper : ∃ f : I → Plane, IsEmbedding f ∧
      f 0 = Plane.mk (-1) 0 ∧ f 1 = Plane.mk 1 0 ∧
      (∀ t, f t ∈ modelCurve) ∧
      (∀ t : I,0<t → t<1 → 0<f t 1) ∧
      Set.range f = {z : Plane | z ∈ modelCurve ∧ 0≤z 1} := by
    as_aux_lemma =>
      let f : I → Plane := fun t => Plane.mk (max (-1) (min 1 (6*(t:ℝ)-3)))
        (min 1 (min (3*(t:ℝ)) (3-3*(t:ℝ))))
      have hfc : Continuous f := by dsimp [f]; fun_prop
      have hleft (t : I) (ht : (t:ℝ) ≤ 1/3) : f t=Plane.mk (-1) (3*(t:ℝ)) := by
        have ha : 6*(t:ℝ)-3 ≤ 1 := by linarith
        have hb : 6*(t:ℝ)-3 ≤ -1 := by linarith
        have hc : 3*(t:ℝ) ≤ 3-3*(t:ℝ) := by linarith
        have hd : 3*(t:ℝ) ≤ 1 := by linarith
        simp only [f,min_eq_right ha,max_eq_left hb,min_eq_left hc,min_eq_right hd]
      have hmid (t : I) (ht0 : 1/3 ≤ (t:ℝ)) (ht1 : (t:ℝ) ≤ 2/3) : f t=Plane.mk (6*(t:ℝ)-3) 1 := by
        have ha : 6*(t:ℝ)-3 ≤ 1 := by linarith
        have hb : -1 ≤ 6*(t:ℝ)-3 := by linarith
        have hc : 1 ≤ min (3*(t:ℝ)) (3-3*(t:ℝ)) := le_min (by linarith) (by linarith)
        simp only [f,min_eq_right ha,max_eq_right hb,min_eq_left hc]
      have hright (t : I) (ht : 2/3 ≤ (t:ℝ)) : f t=Plane.mk 1 (3-3*(t:ℝ)) := by
        have ha : 1 ≤ 6*(t:ℝ)-3 := by linarith
        have hc : 3-3*(t:ℝ) ≤ 3*(t:ℝ) := by linarith
        have hd : 3-3*(t:ℝ) ≤ 1 := by linarith
        simp only [f,min_eq_left ha,max_eq_right (by norm_num : (-1:ℝ)≤1),min_eq_right hc,min_eq_right hd]
      have hclass (t : I) :
          (f t=Plane.mk (-1) (3*(t:ℝ)) ∧ (t:ℝ)≤1/3) ∨
          (f t=Plane.mk (6*(t:ℝ)-3) 1 ∧ 1/3≤(t:ℝ) ∧ (t:ℝ)≤2/3) ∨
          (f t=Plane.mk 1 (3-3*(t:ℝ)) ∧ 2/3≤(t:ℝ)) := by
        by_cases hl : (t:ℝ)≤1/3
        · exact Or.inl ⟨hleft t hl,hl⟩
        · by_cases hr : (t:ℝ)≤2/3
          · exact Or.inr (Or.inl ⟨hmid t (le_of_not_ge hl) hr,le_of_not_ge hl,hr⟩)
          · exact Or.inr (Or.inr ⟨hright t (le_of_not_ge hr),le_of_not_ge hr⟩)
      have hfi : Function.Injective f := by
        as_aux_lemma =>
          intro t u he
          rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
          all_goals rcases hclass u with ⟨hu,hub⟩ | ⟨hu,hub0,hub1⟩ | ⟨hu,hub⟩
          all_goals rw [ht,hu] at he
          all_goals have hx := congrArg (fun z : Plane => z 0) he
          all_goals have hy := congrArg (fun z : Plane => z 1) he
          all_goals simp [Plane.mk] at hx hy
          all_goals apply Subtype.ext
          all_goals nlinarith
      have hcurve (t : I) : f t ∈ modelCurve := by
        as_aux_lemma =>
          change max |f t 0| |f t 1|=1
          rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
          · rw [ht]
            change max |(-1:ℝ)| |3*(t:ℝ)|=1
            rw [abs_neg,abs_one,abs_of_nonneg (by nlinarith [t.property.1]),max_eq_left (by linarith)]
          · rw [ht]
            change max |6*(t:ℝ)-3| |(1:ℝ)|=1
            rw [abs_one,max_eq_right (abs_le.mpr ⟨by linarith,by linarith⟩)]
          · rw [ht]
            change max |(1:ℝ)| |3-3*(t:ℝ)|=1
            rw [abs_one,abs_of_nonneg (by nlinarith [t.property.2]),max_eq_left (by linarith)]
      have hpos (t : I) (ht0 : 0<t) (ht1 : t<1) : 0<f t 1 := by
        rcases hclass t with ⟨ht,htb⟩ | ⟨ht,htb0,htb1⟩ | ⟨ht,htb⟩
        all_goals rw [ht]
        · change 0<3*(t:ℝ); have hh : (0:ℝ)<t := ht0; linarith
        · norm_num [Plane.mk]
        · change 0<3-3*(t:ℝ); have hh : (t:ℝ)<1 := ht1; linarith
      have hf0 : f 0=Plane.mk (-1) 0 := by norm_num [f]
      have hf1 : f 1=Plane.mk 1 0 := by norm_num [f]
      refine ⟨f,(hfc.isClosedEmbedding hfi).isEmbedding,hf0,hf1,hcurve,hpos,?_⟩
      ext v
      constructor
      · rintro ⟨t,rfl⟩
        refine ⟨hcurve t,?_⟩
        by_cases ht0 : t=0
        · rw [ht0,hf0]; norm_num [Plane.mk]
        · by_cases ht1 : t=1
          · rw [ht1,hf1]; norm_num [Plane.mk]
          · exact (hpos t (lt_of_le_of_ne t.property.1 (Ne.symm ht0)) (lt_of_le_of_ne t.property.2 ht1)).le
      · intro hv
        have hmodel : max |v 0| |v 1|=1 := hv.1
        have hx : |v 0|≤1 := (le_max_left _ _).trans hmodel.le
        have hy : v 1≤1 := (le_abs_self _).trans ((le_max_right _ _).trans hmodel.le)
        by_cases hxneg : v 0 = -1
        · let t : I := ⟨v 1/3,⟨by linarith [hv.2],by linarith⟩⟩
          have ht : (t:ℝ)≤1/3 := by dsimp [t]; linarith
          refine ⟨t,?_⟩
          rw [hleft t ht]
          apply PiLp.ext
          intro i
          fin_cases i
          · exact hxneg.symm
          · change 3*(v 1/3)=v 1; ring
        · by_cases hxpos : v 0=1
          · let t : I := ⟨1-v 1/3,⟨by linarith,by linarith [hv.2]⟩⟩
            have ht : 2/3≤(t:ℝ) := by dsimp [t]; linarith
            refine ⟨t,?_⟩
            rw [hright t ht]
            apply PiLp.ext
            intro i
            fin_cases i
            · exact hxpos.symm
            · change 3-3*(1-v 1/3)=v 1; ring
          · have hx0 : -1<v 0 := lt_of_le_of_ne (abs_le.mp hx).1 (Ne.symm hxneg)
            have hx1 : v 0<1 := lt_of_le_of_ne (abs_le.mp hx).2 hxpos
            have hy1 : v 1=1 := by
              as_aux_lemma =>
                apply le_antisymm hy
                by_contra hh
                have hylt : v 1<1 := lt_of_not_ge hh
                have habs : |v 1|<1 := by rw [abs_of_nonneg hv.2]; exact hylt
                have hmax := max_lt (abs_lt.mpr ⟨hx0,hx1⟩) habs
                rw [hmodel] at hmax
                exact lt_irrefl _ hmax
            let t : I := ⟨(v 0+3)/6,⟨by linarith,by linarith⟩⟩
            have ht0 : 1/3≤(t:ℝ) := by dsimp [t]; linarith
            have ht1 : (t:ℝ)≤2/3 := by dsimp [t]; linarith
            refine ⟨t,?_⟩
            rw [hmid t ht0 ht1]
            apply PiLp.ext
            intro i
            fin_cases i
            · change 6*((v 0+3)/6)-3=v 0; ring
            · exact hy1.symm
  have normalize (R : ℝ) (hR : 0 < R) :
      ∃ N : Plane ≃ₜ Plane,
        (∀ z,N z=Plane.mk (z 0/R) (2*z 1/R-1)) ∧
        (∀ z,N z ∈ Plane.openSquare 0 1 ↔ |z 0|<R ∧ 0<z 1 ∧ z 1<R) := by
    apply outsideBandsPackaging_2655_normalize <;> assumption
  have hRpos : 0<R := lt_trans zero_lt_one hR
  obtain ⟨f,hf,hf0,hf1,hfc,hfp,hfim⟩ := upper
  obtain ⟨N,hN,hNopen⟩ := normalize R hRpos
  let fq : I → ↥(Plane.closedSquare 0 1) := fun t => ⟨f t,by
    have hh : max |f t 0| |f t 1|=1 := hfc t
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using hh.le⟩
  have hfqc : Continuous fq := hf.continuous.subtype_mk _
  have hfqi : Function.Injective fq := fun t u he => hf.injective (congrArg Subtype.val he)
  have hfqe : IsEmbedding fq := (hfqc.isClosedEmbedding hfqi).isEmbedding
  let g : I → Plane := B ∘ fq
  have hg : IsEmbedding g := hB.comp hfqe
  have hg0 : g 0=f 0 := by
    have hh := hc ⟨-1,by norm_num⟩
    change B (fq 0)=f 0
    have he : fq 0=⟨Plane.mk (-1) 0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ := Subtype.ext hf0
    rw [he,hf0]
    exact hh
  have hg1 : g 1=f 1 := by
    have hh := hc ⟨1,by norm_num⟩
    change B (fq 1)=f 1
    have he : fq 1=⟨Plane.mk 1 0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ := Subtype.ext hf1
    rw [he,hf1]
    exact hh
  have hmodel (s : ℝ) (hs : |s|≤1) : N (Plane.mk s 0) ∈ modelCurve := by
    rw [hN]
    have hh : max |s/R| |(-1:ℝ)|=1 := by
      rw [abs_div,abs_of_pos hRpos,abs_neg,abs_one,max_eq_right]
      exact (div_le_one hRpos).mpr (hs.trans hR.le)
    simpa [modelCurve,Plane.supNorm,Plane.mk] using hh
  have ha : (N ∘ f) 0 ∈ modelCurve := by
    change N (f 0) ∈ modelCurve
    rw [hf0]
    exact hmodel (-1) (by norm_num)
  have hb : (N ∘ f) 1 ∈ modelCurve := by
    change N (f 1) ∈ modelCurve
    rw [hf1]
    exact hmodel 1 (by norm_num)
  have hfi (t : I) (ht0 : 0<t) (ht1 : t<1) : (N ∘ f) t ∈ Plane.openSquare 0 1 := by
    apply (hNopen (f t)).mpr
    have hm : max |f t 0| |f t 1|=1 := hfc t
    have hp := hfp t ht0 ht1
    refine ⟨lt_of_le_of_lt ((le_max_left _ _).trans hm.le) hR,hp,?_⟩
    exact lt_of_le_of_lt ((le_abs_self _).trans ((le_max_right _ _).trans hm.le)) hR
  have hgi (t : I) (ht0 : 0<t) (ht1 : t<1) : (N ∘ g) t ∈ Plane.openSquare 0 1 := by
    apply (hNopen (g t)).mpr
    have hm := hBU (Set.mem_range_self (fq t))
    have hmR : max |g t 0| |g t 1|<R := by simpa [Plane.openSquare,Plane.supDist,Plane.supNorm,g] using hm
    refine ⟨lt_of_le_of_lt (le_max_left _ _) hmR,hside (fq t) (hfp t ht0 ht1),?_⟩
    exact lt_of_le_of_lt ((le_abs_self _).trans (le_max_right _ _)) hmR
  obtain ⟨P,hP,hPfix⟩ := parametrized_relative_crosscut_replacement
    (N ∘ f) (N ∘ g) (N.isEmbedding.comp hf) (N.isEmbedding.comp hg)
    (congrArg N hg0).symm (congrArg N hg1).symm ha hb hfi hgi
  let F : Plane ≃ₜ Plane := (N.trans P).trans N.symm
  have hfix (z : Plane) (hz : N z ∉ Plane.openSquare 0 1) : F z=z := by
    change N.symm (P (N z))=z
    rw [hPfix _ hz,N.symm_apply_apply]
  refine ⟨F,?_,?_,?_⟩
  · intro z hz
    apply hfix
    intro hNz
    obtain ⟨hx,hy0,hyR⟩ := (hNopen z).mp hNz
    apply hz
    have hh : max |z 0| |z 1|<R := max_lt hx (by rw [abs_of_pos hy0]; exact hyR)
    simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hh
  · intro z hz
    apply hfix
    intro hNz
    exact not_lt_of_ge hz ((hNopen z).mp hNz).2.1
  · intro z hzcurve hzy
    have hz : (z:Plane) ∈ Set.range f := hfim ▸ ⟨hzcurve,hzy⟩
    obtain ⟨t,ht⟩ := hz
    have hq : fq t=z := Subtype.ext ht
    change N.symm (P (N z.val))=B z
    rw [← ht]
    have hh := hP t
    change P (N (f t))=N (g t) at hh
    rw [hh]
    change N.symm (N (B (fq t)))=B z
    rw [N.symm_apply_apply,hq]

private theorem outsideBandsPackaging_3690_tail {S : Type} [TopologicalSpace S] [T2Space S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (y : I) (hy : 0 < y) (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1) :
    ∃ cut : I, 0 < cut ∧ cut < 1 ∧
      ∃ F : I × BandWidth → S, IsEmbedding F ∧
        (∀ w, F (0,w)=D.ends 0
          (⟨δ*w,by constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩,
           ⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩)) ∧
        (∀ w, F (1,w)=D.square (squarePort D.radius D.radius_pos 0 w)) ∧
        (∀ t : I,F (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t)) ∧
        Set.range F ⊆ Set.range (D.ends 0) ∧
        (∀ z, ∃ v : EndRectangle,D.ends 0 v=F z ∧
          (v.1:ℝ)=(δ+(1-δ)*(z.1:ℝ))*(z.2:ℝ) ∧
          (v.2:ℝ) ≤ (y:ℝ) ∧ ((v.2:ℝ)=(y:ℝ) ↔ z.1=0)) ∧
        Set.range F ∩ Set.range D.square =
          Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
        Disjoint (Set.range F) (Set.range D.secondArc) ∧
        (∀ z,F z∈Set.range D.firstArc ↔ (z.2:ℝ)=0) ∧
        D.firstArc cut=D.ends 0 (⟨0,by norm_num⟩,
          ⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩) := by
  have axisParameter {S : Type} [TopologicalSpace S] [T2Space S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ γ : I → I, Continuous γ ∧ StrictAnti γ ∧ γ 0=1 ∧ 0<γ 1 ∧
        (∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
          constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y)) ∧
        ∀ y : I,D.firstArc '' Icc (γ y) 1 ⊆ Set.range (D.ends 0) := by
    apply outsideBandsPackaging_3710_axisParameter <;> assumption
  have reverse {S : Type} [TopologicalSpace S] [T2Space S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (m : I) (hm0 : 0 < m) (hm1 : m < 1)
      (hmends : D.firstArc.symm '' Icc 0 m ⊆ Set.range (D.ends 0)) :
      ∃ E : I × BandWidth → S, IsEmbedding E ∧
        (∀ w, E (0,w) = D.square (squarePort D.radius D.radius_pos 0 w)) ∧
        (∀ t : I, E (t,⟨0,by norm_num⟩) = D.firstArc.symm.extend ((m : ℝ)*t)) ∧
        Set.range E ∩ Set.range D.firstArc.symm = D.firstArc.symm '' Icc 0 m ∧
        Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
        Disjoint (Set.range E) (Set.range D.secondArc) ∧
        ∃ height : I → BandWidth, Continuous height ∧ StrictMono height ∧ height 0 = ⟨0,by norm_num⟩ ∧
          ∀ z, E z = D.ends 0 (z.2,height z.1) := by
    apply outsideBandsPackaging_3777_reverse <;> assumption
  obtain ⟨γ,hγc,hγanti,hγ0,hγ1,hγ,hγtail⟩ := axisParameter D
  let cut := γ y
  have hcut0 : 0 < cut := hγ1.trans_le (hγanti.antitone y.property.2)
  have hcut1 : cut < 1 := by have hh := hγanti hy; simpa [hγ0] using hh
  let m : I := ⟨1-(cut:ℝ),⟨by have hh : (cut:ℝ)<1 := hcut1; linarith,
    by have hh : 0<(cut:ℝ) := hcut0; linarith⟩⟩
  have hm0 : 0 < m := by change 0<1-(cut:ℝ); exact sub_pos.mpr hcut1
  have hm1 : m < 1 := by change 1-(cut:ℝ)<1; have hh : 0<(cut:ℝ) := hcut0; linarith
  have hmends : D.firstArc.symm '' Icc 0 m ⊆ Set.range (D.ends 0) := by
    as_aux_lemma =>
      rintro x ⟨t,ht,rfl⟩
      rw [Path.symm_apply]
      apply hγtail y
      refine ⟨unitInterval.symm t,⟨?_,(unitInterval.symm t).property.2⟩,rfl⟩
      change (cut:ℝ)≤1-(t:ℝ)
      have hh : (t:ℝ)≤1-(cut:ℝ) := ht.2
      linarith
  obtain ⟨E,hE,hE0,hcenter,_,hEq,hother,height,hheight,hmono,hzero,hformula⟩ :=
    reverse D m hm0 hm1 hmends
  have hheight1 : height 1=⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩ := by
    as_aux_lemma =>
      have hEc : E (1,⟨0,by norm_num⟩)=D.ends 0
          (⟨0,by norm_num⟩,⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩) := by
        rw [hcenter,Path.extend_symm_apply]
        have htime : 1-(m:ℝ)*(1:I)=(cut:ℝ) := by dsimp [m]; simp
        rw [htime,Path.extend_extends']
        exact (hγ y).symm
      have hh := (D.ends_embedded 0).injective ((hformula (1,⟨0,by norm_num⟩)).symm.trans hEc)
      exact congrArg (fun p : EndRectangle => p.2) hh
  let scale : I → ℝ := fun t => δ+(1-δ)*(t:ℝ)
  have hs (t : I) : 0<scale t ∧ scale t≤1 := by
    dsimp [scale]
    have hnon := mul_nonneg (sub_nonneg.mpr hδ.2) t.property.1
    have hupper := mul_le_mul_of_nonneg_left t.property.2 (sub_nonneg.mpr hδ.2)
    constructor <;> linarith [hδ.1]
  let k : I × BandWidth → I × BandWidth := fun z =>
    (unitInterval.symm z.1,⟨scale z.1*(z.2:ℝ),by
      constructor <;> nlinarith [z.2.property.1,z.2.property.2,(hs z.1).1,(hs z.1).2]⟩)
  have hkc : Continuous k := by dsimp [k,scale]; fun_prop
  have hki : Function.Injective k := by
    as_aux_lemma =>
      intro z w he
      have ht : z.1=w.1 := unitInterval.symm_involutive.injective (congrArg Prod.fst he)
      apply Prod.ext ht
      apply Subtype.ext
      have hw := congrArg (fun q : I × BandWidth => (q.2:ℝ)) he
      change scale z.1*(z.2:ℝ)=scale w.1*(w.2:ℝ) at hw
      rw [←ht] at hw
      exact mul_left_cancel₀ (hs z.1).1.ne' hw
  let F := E ∘ k
  have hF : IsEmbedding F := hE.comp ((hkc.isClosedEmbedding hki).isEmbedding)
  have hF0 (w : BandWidth) : F (0,w)=D.ends 0
      (⟨δ*w,by constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩,⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩) := by
    as_aux_lemma =>
      change E (k (0,w))=_
      rw [hformula]
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        simp [k,scale]
      · simp [k,hheight1]
  have hF1 (w : BandWidth) : F (1,w)=D.square (squarePort D.radius D.radius_pos 0 w) := by
    have hk : k (1,w)=(0,w) := by
      apply Prod.ext
      · simp [k]
      · apply Subtype.ext; simp [k,scale]
    change E (k (1,w))=_
    rw [hk,hE0]
  refine ⟨cut,hcut0,hcut1,F,hF,hF0,hF1,?_,?_,?_,?_,?_,?_,(hγ y).symm⟩
  · intro t
    have hk : k (t,⟨0,by norm_num⟩)=(unitInterval.symm t,⟨0,by norm_num⟩) := by
      apply Prod.ext
      · rfl
      · apply Subtype.ext; simp [k]
    change E (k (t,⟨0,by norm_num⟩))=_
    rw [hk,hcenter,Path.extend_symm_apply]
    congr 1
    change 1-(m:ℝ)*(1-(t:ℝ))=(cut:ℝ)+(1-(cut:ℝ))*t
    dsimp [m]
    ring
  · rintro x ⟨z,rfl⟩
    exact ⟨((k z).2,height (k z).1),(hformula (k z)).symm⟩
  · intro z
    refine ⟨((k z).2,height (k z).1),(hformula (k z)).symm,rfl,?_,?_⟩
    · have hh := hmono.monotone (show (k z).1 ≤ (1:I) from (k z).1.property.2)
      rw [hheight1] at hh
      exact hh
    · constructor
      · intro hh
        have he : height (k z).1=height 1 := Subtype.ext (by simpa [hheight1] using hh)
        have ht := hmono.injective he
        have htR := congrArg Subtype.val ht
        change 1-(z.1:ℝ)=1 at htR
        apply Subtype.ext
        change (z.1:ℝ)=0
        linarith
      · intro hz
        have hh : (k z).1=1 := by change unitInterval.symm z.1=1; rw [hz]; simp
        rw [hh,hheight1]
  · ext x
    constructor
    · rintro ⟨⟨z,rfl⟩,hz⟩
      have hh : F z∈Set.range E ∩ Set.range D.square := ⟨Set.mem_range_self (k z),hz⟩
      exact hEq ▸ hh
    · rintro ⟨w,rfl⟩
      exact ⟨⟨(1,w),hF1 w⟩,Set.mem_range_self _⟩
  · apply hother.mono_left
    rintro x ⟨z,rfl⟩
    exact Set.mem_range_self (k z)
  · intro z
    constructor
    · intro hz
      have hza : F z ∈ a.image := (D.firstArc_range ▸ hz).1
      have hh := ((D.ends_axes 0 ((k z).2,height (k z).1)).1.mp
        ((hformula (k z)).symm ▸ hza)).2
      change scale z.1*(z.2:ℝ)=0 at hh
      exact (mul_eq_zero.mp hh).resolve_left (hs z.1).1.ne'
    · intro hz
      have hw : z.2=⟨0,by norm_num⟩ := Subtype.ext hz
      rw [show F z=F (z.1,⟨0,by norm_num⟩) by rw [←hw]]
      change E (k (z.1,⟨0,by norm_num⟩)) ∈ Set.range D.firstArc
      have hk : k (z.1,⟨0,by norm_num⟩)=(unitInterval.symm z.1,⟨0,by norm_num⟩) := by
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [k]
      rw [hk,hcenter,Path.extend_symm_apply]
      exact D.firstArc.extend_range ▸ Set.mem_range_self _

private theorem outsideBandsPackaging_903_paste_prefix {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m : I) (hm0 : 0 < m) (hm1 : m < 1)
    (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
    (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
    (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
    (h : ℝ) (hh : 0 < h ∧ (m : ℝ)+h < 1)
    (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda ≤ 1)
    (R : I × Icc (-1 : ℝ) 1 → S) (hR : IsEmbedding R)
    (hRport : ∀ w : Icc (-1 : ℝ) 1, R (0,w) = E (1,⟨lambda*w,by constructor <;> nlinarith [w.property.1,w.property.2,hlambda.1,hlambda.2]⟩))
    (hRc : ∀ t : I, R (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+h*t))
    (hRE : Set.range R ∩ Set.range E = Set.range (fun w : Icc (-1 : ℝ) 1 => R (0,w)))
    (hRmeet : Set.range R ∩ Set.range p = p '' Icc m ⟨(m : ℝ)+h,by constructor <;> linarith [m.property.1,hh.1]⟩)
    (U : Set S) (hRU : Set.range R ⊆ U) :
    ∃ G : I × Icc (-1 : ℝ) 1 → S,
      IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
      (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend (((m : ℝ)+h)*t)) ∧
      Set.range G ∩ Set.range p = p '' Icc 0 ⟨(m : ℝ)+h,by constructor <;> linarith [m.property.1,hh.1]⟩ ∧
      Set.range G ⊆ Set.range E ∪ U := by
  have taper     (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (lambda : ℝ) (hl : 0 < lambda ∧ lambda ≤ 1) :
      ∃ F : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding F ∧ Set.range F ⊆ Set.range E ∧
        (∀ t : I, F (t,⟨0,by norm_num⟩) = E (t,⟨0,by norm_num⟩)) ∧
        (∀ w : Icc (-1 : ℝ) 1, F (0,w) = E (0,w)) ∧
        (∀ w : Icc (-1 : ℝ) 1, F (1,w) = E (1,⟨lambda*w,by constructor <;> nlinarith [w.property.1,w.property.2]⟩)) := by
    as_aux_lemma =>
      let scale : I → ℝ := fun t => 1-(1-lambda)*t
      have hs (t : I) : 0 < scale t ∧ scale t ≤ 1 := by
        dsimp [scale]
        constructor <;> nlinarith [t.property.1,t.property.2,hl.1,hl.2]
      let a : I × Icc (-1 : ℝ) 1 → I × Icc (-1 : ℝ) 1 := fun z =>
        (z.1,⟨scale z.1*z.2,by
          constructor
          · have hh := mul_le_mul_of_nonneg_left z.2.property.1 (hs z.1).1.le
            nlinarith [(hs z.1).2]
          · have hh := mul_le_mul_of_nonneg_left z.2.property.2 (hs z.1).1.le
            nlinarith [(hs z.1).2]⟩)
      have hac : Continuous a := by dsimp [a,scale]; fun_prop
      have hai : Function.Injective a := by
        as_aux_lemma =>
          intro z w heq
          have ht : z.1 = w.1 := by simpa [a] using congrArg Prod.fst heq
          apply Prod.ext ht
          apply Subtype.ext
          have hw := congrArg (fun z : I × Icc (-1 : ℝ) 1 => (z.2 : ℝ)) heq
          change scale z.1*z.2 = scale w.1*w.2 at hw
          rw [←ht] at hw
          exact mul_left_cancel₀ (hs z.1).1.ne' hw
      let F := E ∘ a
      refine ⟨F,hE.comp ((hac.isClosedEmbedding hai).isEmbedding),?_,?_,?_,?_⟩
      · rintro y ⟨z,rfl⟩; exact Set.mem_range_self _
      · intro t
        apply congrArg E
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [a]
      · intro w
        apply congrArg E
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [a,scale]
      · intro w
        apply congrArg E
        apply Prod.ext
        · rfl
        · apply Subtype.ext; simp [a,scale]
  have paste     (L R : I × Icc (-1 : ℝ) 1 → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
      (hport : ∀ w : Icc (-1 : ℝ) 1, L (0,w) = R (0,w))
      (hsep : Set.range L ∩ Set.range R = Set.range (fun w : Icc (-1 : ℝ) 1 => R (0,w))) :
      ∃ F : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding F ∧
        (∀ w, F (0,w) = L (1,w)) ∧
        (∀ w, F (1,w) = R (1,w)) ∧
        (∀ w, F (⟨1/2,by norm_num⟩,w) = L (0,w)) ∧
        Set.range F = Set.range L ∪ Set.range R ∧
        (∀ (t : I) (w : Icc (-1 : ℝ) 1), (t : ℝ) ≤ 1/2 →
          F (t,w) = L (projIcc 0 1 zero_le_one (1-2*(t : ℝ)),w)) ∧
        (∀ (t : I) (w : Icc (-1 : ℝ) 1), 1/2 ≤ (t : ℝ) →
          F (t,w) = R (projIcc 0 1 zero_le_one (2*(t : ℝ)-1),w)) ∧
        F '' (Ici (⟨1/2,by norm_num⟩ : I) ×ˢ Set.univ) = Set.range R := by
    as_aux_lemma =>
      classical
      let kl (z : I × Icc (-1 : ℝ) 1) : I × Icc (-1 : ℝ) 1 :=
        (projIcc 0 1 zero_le_one (1-2*(z.1:ℝ)),z.2)
      let kr (z : I × Icc (-1 : ℝ) 1) : I × Icc (-1 : ℝ) 1 :=
        (projIcc 0 1 zero_le_one (2*(z.1:ℝ)-1),z.2)
      let F : I × Icc (-1 : ℝ) 1 → S := fun z => if (z.1:ℝ) ≤ 1/2 then L (kl z) else R (kr z)
      have hklc : Continuous kl := by dsimp [kl]; fun_prop
      have hkrc : Continuous kr := by dsimp [kr]; fun_prop
      have hfc : Continuous F := by
        apply continuous_if_le (by fun_prop) continuous_const
          (hL.continuous.comp hklc).continuousOn (hR.continuous.comp hkrc).continuousOn
        intro z hz
        have hl : kl z = (0,z.2) := by
          apply Prod.ext
          · apply Subtype.ext
            simp [kl,hz]
          · rfl
        have hr : kr z = (0,z.2) := by
          apply Prod.ext
          · apply Subtype.ext
            simp [kr,hz]
          · rfl
        change L (kl z) = R (kr z)
        rw [hl,hr,hport]
      have hleft (z : I × Icc (-1 : ℝ) 1) (hz : (z.1:ℝ) ≤ 1/2) :
          ((kl z).1:ℝ) = 1-2*(z.1:ℝ) := by
        exact congrArg Subtype.val (projIcc_of_mem zero_le_one
          (show 1-2*(z.1:ℝ) ∈ I from ⟨by linarith,by linarith [z.1.property.1]⟩))
      have hright (z : I × Icc (-1 : ℝ) 1) (hz : 1/2 ≤ (z.1:ℝ)) :
          ((kr z).1:ℝ) = 2*(z.1:ℝ)-1 := by
        exact congrArg Subtype.val (projIcc_of_mem zero_le_one
          (show 2*(z.1:ℝ)-1 ∈ I from ⟨by linarith,by linarith [z.1.property.2]⟩))
      have hfi : Function.Injective F := by
        as_aux_lemma =>
          intro z w he
          dsimp only [F] at he
          split_ifs at he with hz hw hw
          · have hh := hL.injective he
            apply Prod.ext
            · apply Subtype.ext
              have h1 := congrArg (fun a : I × Icc (-1 : ℝ) 1 => (a.1:ℝ)) hh
              rw [hleft z hz,hleft w hw] at h1
              linarith
            · simpa [kl] using congrArg Prod.snd hh
          · have hm : L (kl z) ∈ Set.range L ∩ Set.range R :=
              ⟨Set.mem_range_self _,⟨kr w,he.symm⟩⟩
            rw [hsep] at hm
            obtain ⟨u,hu⟩ := hm
            have hr : R (kr w) = R (0,u) := he.symm.trans hu.symm
            have h1 := congrArg (fun a : I × Icc (-1 : ℝ) 1 => (a.1:ℝ)) (hR.injective hr)
            rw [hright w (by linarith)] at h1
            norm_num at h1
            exfalso
            linarith
          · have hm : L (kl w) ∈ Set.range L ∩ Set.range R :=
              ⟨Set.mem_range_self _,⟨kr z,he⟩⟩
            rw [hsep] at hm
            obtain ⟨u,hu⟩ := hm
            have hr : R (kr z) = R (0,u) := he.trans hu.symm
            have h1 := congrArg (fun a : I × Icc (-1 : ℝ) 1 => (a.1:ℝ)) (hR.injective hr)
            rw [hright z (by linarith)] at h1
            norm_num at h1
            exfalso
            linarith
          · have hh := hR.injective he
            apply Prod.ext
            · apply Subtype.ext
              have h1 := congrArg (fun a : I × Icc (-1 : ℝ) 1 => (a.1:ℝ)) hh
              rw [hright z (by linarith),hright w (by linarith)] at h1
              linarith
            · simpa [kr] using congrArg Prod.snd hh
      refine ⟨F,(hfc.isClosedEmbedding hfi).isEmbedding,?_,?_,?_,?_,?_,?_,?_⟩
      · intro w
        simp [F,kl]
      · intro w
        norm_num [F,kr]
      · intro w
        simp [F,kl]
      · ext x
        constructor
        · rintro ⟨z,rfl⟩
          dsimp only [F]
          split_ifs
          · exact Or.inl (Set.mem_range_self _)
          · exact Or.inr (Set.mem_range_self _)
        · rintro (⟨z,rfl⟩ | ⟨z,rfl⟩)
          · let t : I := ⟨(1-(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
            have ht : (t:ℝ) ≤ 1/2 := by dsimp [t]; linarith [z.1.property.1]
            refine ⟨(t,z.2),?_⟩
            rw [show F (t,z.2) = L (kl (t,z.2)) from if_pos ht]
            apply congrArg L
            apply Prod.ext
            · apply Subtype.ext
              rw [hleft _ ht]
              dsimp [t]
              ring
            · rfl
          · let t : I := ⟨(1+(z.1:ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
            by_cases hz0 : z.1 = 0
            · have hz : z = (0,z.2) := Prod.ext hz0 rfl
              refine ⟨(⟨1/2,by norm_num⟩,z.2),?_⟩
              rw [hz]
              norm_num [F,kl,hport]
            · have ht : 1/2 < (t:ℝ) := by
                have hp : 0 < z.1 := lt_of_le_of_ne z.1.property.1 (fun h => hz0 h.symm)
                have hp' : (0:ℝ) < z.1 := hp
                dsimp [t]
                exact (by linarith : (1+(z.1:ℝ))/2 > 1/2)
              refine ⟨(t,z.2),?_⟩
              rw [show F (t,z.2) = R (kr (t,z.2)) from if_neg (not_le.mpr ht)]
              apply congrArg R
              apply Prod.ext
              · apply Subtype.ext
                rw [hright _ ht.le]
                dsimp [t]
                ring
              · rfl
      · intro t w ht
        exact if_pos ht
      · intro t w ht
        by_cases htt : (t : ℝ) ≤ 1/2
        · have heq : (t : ℝ) = 1/2 := le_antisymm htt ht
          have hl : kl (t,w) = (0,w) := by
            apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp [kl,heq])
          have hr : kr (t,w) = (0,w) := by
            apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp [kr,heq])
          change F (t,w) = R (kr (t,w))
          rw [show F (t,w) = L (kl (t,w)) from if_pos htt,hl,hr,hport]
        · exact if_neg htt
      · ext y
        constructor
        · rintro ⟨z,hz,rfl⟩
          have ht : 1/2 ≤ (z.1 : ℝ) := hz.1
          by_cases htt : (z.1 : ℝ) ≤ 1/2
          · have heq : (z.1 : ℝ) = 1/2 := le_antisymm htt ht
            have hl : kl z = (0,z.2) := by
              apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp [kl,heq])
            rw [show F z = L (kl z) from if_pos htt,hl,hport]
            exact Set.mem_range_self _
          · rw [show F z = R (kr z) from if_neg htt]
            exact Set.mem_range_self _
        · rintro ⟨z,rfl⟩
          let t : I := ⟨(1+(z.1 : ℝ))/2,by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩
          have ht : 1/2 ≤ (t : ℝ) := by dsimp [t]; linarith [z.1.property.1]
          refine ⟨(t,z.2),⟨ht,Set.mem_univ _⟩,?_⟩
          by_cases htt : (t : ℝ) ≤ 1/2
          · have hzt : (z.1 : ℝ) = 0 := by dsimp [t] at htt; linarith [z.1.property.1]
            have heq : (t : ℝ) = 1/2 := le_antisymm htt ht
            have hl : kl (t,z.2) = (0,z.2) := by
              apply Prod.ext <;> first | rfl | (apply Subtype.ext; simp [kl,heq])
            have hz : z = (0,z.2) := Prod.ext (Subtype.ext hzt) rfl
            rw [show F (t,z.2) = L (kl (t,z.2)) from if_pos htt,hl,hport,hz]
          · rw [show F (t,z.2) = R (kr (t,z.2)) from if_neg htt]
            apply congrArg R
            apply Prod.ext
            · apply Subtype.ext
              rw [hright _ ht]
              dsimp [t]
              ring
            · rfl
  have joinTime (q : ℝ) (hq : 0 < q ∧ q < 1) :
      ∃ f : I → I, Continuous f ∧ Function.Injective f ∧ f 0 = 0 ∧ f 1 = 1 ∧
        (∀ t : I, (t : ℝ) ≤ q → (f t : ℝ) = (t : ℝ)/(2*q)) ∧
        (∀ t : I, q ≤ (t : ℝ) → (f t : ℝ) = 1/2+((t : ℝ)-q)/(2*(1-q))) := by
    as_aux_lemma =>
      have hd : 0 < 2*q := by linarith [hq.1]
      have hd' : 0 < 2*(1-q) := by linarith [hq.2]
      let g : I → ℝ := fun t => if (t : ℝ) ≤ q then (t : ℝ)/(2*q)
        else 1/2+((t : ℝ)-q)/(2*(1-q))
      have hleft (t : I) (ht : (t : ℝ) ≤ q) : 0 ≤ g t ∧ g t ≤ 1/2 := by
        rw [show g t = (t : ℝ)/(2*q) from if_pos ht]
        refine ⟨div_nonneg t.property.1 hd.le,?_⟩
        apply (div_le_iff₀ hd).mpr
        nlinarith
      have hright (t : I) (ht : q < (t : ℝ)) : 1/2 < g t ∧ g t ≤ 1 := by
        as_aux_lemma =>
          rw [show g t = 1/2+((t : ℝ)-q)/(2*(1-q)) from if_neg (not_le_of_gt ht)]
          constructor
          · linarith [div_pos (sub_pos.mpr ht) hd']
          · have hh : ((t : ℝ)-q)/(2*(1-q)) ≤ 1/2 := by
              apply (div_le_iff₀ hd').mpr
              nlinarith [t.property.2]
            linarith
      have hg (t : I) : g t ∈ I := by
        by_cases ht : (t : ℝ) ≤ q
        · obtain ⟨h0,h1⟩ := hleft t ht; exact ⟨h0,by linarith⟩
        · obtain ⟨h0,h1⟩ := hright t (lt_of_not_ge ht); exact ⟨by linarith,h1⟩
      have hgc : Continuous g := by
        apply continuous_if_le (by fun_prop) continuous_const
          (show ContinuousOn (fun t : I => (t : ℝ)/(2*q)) _ from by fun_prop)
          (show ContinuousOn (fun t : I => 1/2+((t : ℝ)-q)/(2*(1-q))) _ from by fun_prop)
        intro t ht
        rw [ht]
        field_simp [hq.1.ne']
        <;> ring
      let f : I → I := fun t => ⟨g t,hg t⟩
      have hfi : Function.Injective f := by
        as_aux_lemma =>
          intro t u hh
          have heq := congrArg Subtype.val hh
          change g t = g u at heq
          by_cases ht : (t : ℝ) ≤ q
          · by_cases hu : (u : ℝ) ≤ q
            · change (if (t : ℝ) ≤ q then _ else _) = (if (u : ℝ) ≤ q then _ else _) at heq
              rw [if_pos ht,if_pos hu] at heq
              exact Subtype.ext ((div_left_inj' hd.ne').mp heq)
            · have htl := (hleft t ht).2
              have hur := (hright u (lt_of_not_ge hu)).1
              linarith
          · by_cases hu : (u : ℝ) ≤ q
            · have htr := (hright t (lt_of_not_ge ht)).1
              have hul := (hleft u hu).2
              linarith
            · change (if (t : ℝ) ≤ q then _ else _) = (if (u : ℝ) ≤ q then _ else _) at heq
              rw [if_neg ht,if_neg hu] at heq
              have hhDiv : ((t : ℝ)-q)/(2*(1-q)) = ((u : ℝ)-q)/(2*(1-q)) := by linarith
              have hhSub := (div_left_inj' hd'.ne').mp hhDiv
              apply Subtype.ext
              linarith
      refine ⟨f,hgc.subtype_mk _,hfi,?_,?_,?_,?_⟩
      · apply Subtype.ext
        simp [f,g,hq.1.le]
      · apply Subtype.ext
        have hnot : ¬ (1 : ℝ) ≤ q := not_le_of_gt hq.2
        change (if (1 : ℝ) ≤ q then (1 : ℝ)/(2*q) else 1/2+((1 : ℝ)-q)/(2*(1-q))) = 1
        rw [if_neg hnot]
        field_simp [(sub_pos.mpr hq.2).ne']
        <;> ring
      · intro t ht; exact if_pos ht
      · intro t ht
        by_cases htt : (t : ℝ) ≤ q
        · have hh : (t : ℝ) = q := le_antisymm htt ht
          change (if (t : ℝ) ≤ q then _ else _) = _
          rw [if_pos htt,hh]
          field_simp [hq.1.ne']
          <;> ring
        · exact if_neg htt
  obtain ⟨T,hT,hTE,hTc,hT0,hT1⟩ := taper E hE lambda hlambda
  let b : I × Icc (-1 : ℝ) 1 → I × Icc (-1 : ℝ) 1 := fun z =>
    (⟨1-(z.1 : ℝ),by constructor <;> linarith [z.1.property.1,z.1.property.2]⟩,z.2)
  have hbc : Continuous b := by dsimp [b]; fun_prop
  have hbi : Function.Injective b := by
    intro z w heq
    apply Prod.ext
    · apply Subtype.ext
      have hh := congrArg (fun z : I × Icc (-1 : ℝ) 1 => (z.1 : ℝ)) heq
      dsimp [b] at hh; linarith
    · simpa [b] using congrArg Prod.snd heq
  let L := T ∘ b
  have hL : IsEmbedding L := hT.comp ((hbc.isClosedEmbedding hbi).isEmbedding)
  have hLE : Set.range L ⊆ Set.range E := by
    rintro y ⟨z,rfl⟩; exact hTE (Set.mem_range_self (b z))
  have hport (w : Icc (-1 : ℝ) 1) : L (0,w) = R (0,w) := by
    simpa [L,b] using (hT1 w).trans (hRport w).symm
  have hsep : Set.range L ∩ Set.range R = Set.range (fun w : Icc (-1 : ℝ) 1 => R (0,w)) := by
    ext y; constructor
    · rintro ⟨hyL,hyR⟩
      have hy : y ∈ Set.range R ∩ Set.range E := ⟨hyR,hLE hyL⟩
      exact hRE ▸ hy
    · rintro ⟨w,rfl⟩
      exact ⟨⟨(0,w),hport w⟩,Set.mem_range_self _⟩
  obtain ⟨F,hF,hF0,hF1,hFmid,hFunion,hFleft,hFright,hFpositive⟩ := paste L R hL hR hport hsep
  let n : I := ⟨(m : ℝ)+h,by constructor <;> linarith [m.property.1,hh.1,hh.2]⟩
  have hn : m < n := by change (m : ℝ) < (m : ℝ)+h; linarith [hh.1]
  have hn1 : n < 1 := hh.2
  let q : ℝ := (m : ℝ)/((m : ℝ)+h)
  have hmR : 0 < (m : ℝ) := hm0
  have hsum : 0 < (m : ℝ)+h := by linarith [hh.1]
  have hq : 0 < q ∧ q < 1 := ⟨div_pos hmR hsum,(div_lt_one hsum).mpr (by linarith [hh.1])⟩
  obtain ⟨f,hfc,hfi,hf0,hf1,hfleft,hfright⟩ := joinTime q hq
  let v : I × Icc (-1 : ℝ) 1 → I × Icc (-1 : ℝ) 1 := fun z => (f z.1,z.2)
  have hvc : Continuous v := by dsimp [v]; fun_prop
  have hvi : Function.Injective v := by
    intro z w heq
    apply Prod.ext
    · exact hfi (congrArg Prod.fst heq)
    · simpa [v] using congrArg Prod.snd heq
  let G := F ∘ v
  have hG : IsEmbedding G := hF.comp ((hvc.isClosedEmbedding hvi).isEmbedding)
  have hG0 (w : Icc (-1 : ℝ) 1) : G (0,w) = E (0,w) := by
    change F (f 0,w) = _
    rw [hf0,hF0]
    simpa [L,b] using hT0 w
  have hGcenter (t : I) : G (t,⟨0,by norm_num⟩) = p.extend ((n : ℝ)*t) := by
    as_aux_lemma =>
      change F (f t,⟨0,by norm_num⟩) = _
      by_cases ht : (t : ℝ) ≤ q
      · have hfhalf : (f t : ℝ) ≤ 1/2 := by
          rw [hfleft t ht]
          apply (div_le_iff₀ (show 0 < 2*q by linarith [hq.1])).mpr
          nlinarith
        rw [hFleft _ _ hfhalf]
        change T (b (_,⟨0,by norm_num⟩)) = _
        rw [hTc,hcenter]
        have hu := congrArg Subtype.val (projIcc_of_mem zero_le_one
          (show 1-2*(f t : ℝ) ∈ I from ⟨by linarith,by linarith [(f t).property.1]⟩))
        change p.extend ((m : ℝ)*(1-(projIcc 0 1 zero_le_one (1-2*(f t : ℝ)) : ℝ))) = _
        congr 1
        change (m : ℝ)*(1-(projIcc 0 1 zero_le_one (1-2*(f t : ℝ)) : ℝ)) = (n : ℝ)*t
        apply (congrArg (fun u : ℝ => (m : ℝ)*(1-u)) hu).trans
        change (m : ℝ)*(1-(1-2*(f t : ℝ))) = (n : ℝ)*t
        rw [hfleft t ht]
        dsimp [q,n]
        field_simp [hmR.ne',hsum.ne']
        <;> ring
      · have hft : 1/2 ≤ (f t : ℝ) := by
          rw [hfright t (le_of_not_ge ht)]
          have hh := div_nonneg (sub_nonneg.mpr (le_of_not_ge ht))
            (show 0 ≤ 2*(1-q) by linarith [hq.2])
          linarith
        rw [hFright _ _ hft,hRc]
        have hu := congrArg Subtype.val (projIcc_of_mem zero_le_one
          (show 2*(f t : ℝ)-1 ∈ I from ⟨by linarith,by linarith [(f t).property.2]⟩))
        congr 1
        change (m : ℝ)+h*(projIcc 0 1 zero_le_one (2*(f t : ℝ)-1) : ℝ) = (n : ℝ)*t
        apply (congrArg (fun u : ℝ => (m : ℝ)+h*u) hu).trans
        change (m : ℝ)+h*(2*(f t : ℝ)-1) = (n : ℝ)*t
        rw [hfright t (le_of_not_ge ht)]
        dsimp [q,n]
        field_simp [hmR.ne',hsum.ne',hh.1.ne']
        <;> ring
  have hGsub : Set.range G ⊆ Set.range E ∪ U := by
    rintro y ⟨z,rfl⟩
    have hy : F (v z) ∈ Set.range L ∪ Set.range R := hFunion ▸ Set.mem_range_self (v z)
    rcases hy with hy | hy
    · exact Or.inl (hLE hy)
    · exact Or.inr (hRU hy)
  have hGmeet : Set.range G ∩ Set.range p = p '' Icc 0 n := by
    as_aux_lemma =>
      ext y; constructor
      · rintro ⟨⟨z,rfl⟩,⟨s,hs⟩⟩
        have hy : G z ∈ Set.range L ∪ Set.range R := hFunion ▸ Set.mem_range_self (v z)
        rcases hy with hyL | hyR
        · have hym : G z ∈ Set.range E ∩ Set.range p := ⟨hLE hyL,⟨s,hs⟩⟩
          obtain ⟨u,hu,huEq⟩ := hmeet ▸ hym
          have hu0 : (0 : I) ≤ u := hu.1
          have hum : (u : ℝ) ≤ m := hu.2
          exact ⟨u,⟨hu0,show u ≤ n by change (u : ℝ) ≤ (m : ℝ)+h; linarith [hh.1]⟩,huEq⟩
        · have hym : G z ∈ Set.range R ∩ Set.range p := ⟨hyR,⟨s,hs⟩⟩
          obtain ⟨u,hu,huEq⟩ := hRmeet ▸ hym
          exact ⟨u,⟨u.property.1,hu.2⟩,huEq⟩
      · rintro ⟨s,hs,rfl⟩
        let t : I := ⟨(s : ℝ)/n,⟨div_nonneg s.property.1 hsum.le,
          (div_le_one hsum).mpr (show (s : ℝ) ≤ n from hs.2)⟩⟩
        have ht : (n : ℝ)*t = s := mul_div_cancel₀ _ hsum.ne'
        refine ⟨⟨(t,⟨0,by norm_num⟩),?_⟩,Set.mem_range_self _⟩
        rw [hGcenter,ht,p.extend_apply s.property]
  exact ⟨G,hG,hG0,hGcenter,hGmeet,hGsub⟩

private theorem outsideBandsPackaging_2517_positive (R : ℝ) (hR : 1<R)
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hBU : Set.range B ⊆ Plane.openSquare 0 R)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
      (∀ z, z 1≤0 → H z=z) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 1 → H z=B z := by
  have boundary (R : ℝ) (hR : 1<R)
      (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hBU : Set.range B ⊆ Plane.openSquare 0 R)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
      ∃ F : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 R → F z=z) ∧
        (∀ z, z 1≤0 → F z=z) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),
          z.val ∈ modelCurve → 0≤z.val 1 → F z = B z := by
    apply outsideBandsPackaging_2527_boundary <;> assumption
  have sameRange (e f : ↥(Plane.closedSquare 0 1) → Plane) (he : IsEmbedding e) (hf : IsEmbedding f)
      (hag : ∀ z : ↥(Plane.closedSquare 0 1), z.val ∈ modelCurve → e z=f z) :
      Set.range e=Set.range f := by
    apply outsideBandsPackaging_2777_sameRange <;> assumption
  have patch (A : Set Plane) (hA : IsClosed A) (e : A ≃ₜ A)
      (he : ∀ (x : A), (x : Plane) ∈ frontier A → (e x : Plane) = x) :
      ∃ H : Plane ≃ₜ Plane,
        (∀ x : A,H x = e x) ∧ (∀ x, x ∉ interior A → H x = x) := by
    apply outsideBandsPackaging_2923_patch <;> assumption
  classical
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  have bounds (z : Q) : |z.val 0|≤1 ∧ |z.val 1|≤1 := by
    have hh : max |z.val 0| |z.val 1|≤1 := by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
    exact ⟨(le_max_left _ _).trans hh,(le_max_right _ _).trans hh⟩
  let J : Q → Q := fun z => ⟨Plane.mk (z.val 0) ((z.val 1+1)/2),by
    have hz := bounds z
    have hy : |(z.val 1+1)/2|≤1 := abs_le.mpr ⟨by nlinarith [(abs_le.mp hz.2).1],by nlinarith [(abs_le.mp hz.2).2]⟩
    simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hz.1 hy⟩
  have hJc : Continuous J := by dsimp [J]; fun_prop
  have hJi : Function.Injective J := by
    as_aux_lemma =>
      intro z w he
      have hx := congrArg (fun z : Q => z.val 0) he
      have hy := congrArg (fun z : Q => z.val 1) he
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · exact hx
      · change (z.val 1+1)/2=(w.val 1+1)/2 at hy
        change z.val 1=w.val 1
        linarith
  have hJe : IsEmbedding J := (hJc.isClosedEmbedding hJi).isEmbedding
  have hJpos (z : Q) : 0≤(J z).val 1 := by
    change 0≤(z.val 1+1)/2
    nlinarith [(abs_le.mp (bounds z).2).1]
  have axisB (z : Q) (hz : z.val 1=0) : B z=z := by
    as_aux_lemma =>
      let t : Icc (-1 : ℝ) 1 := ⟨z.val 0,abs_le.mp (bounds z).1⟩
      have he : z=⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
        apply Subtype.ext
        apply PiLp.ext
        intro i
        fin_cases i
        · rfl
        · exact hz
      rw [he,hc]
  have hJboundary (z : Q) (hz : z.val ∈ modelCurve) :
      (J z).val 1=0 ∨ (J z).val ∈ modelCurve := by
    as_aux_lemma =>
      have hm : max |z.val 0| |z.val 1|=1 := hz
      by_cases hy : z.val 1= -1
      · left
        change (z.val 1+1)/2=0
        rw [hy]; norm_num
      · right
        have hb := bounds z
        by_cases hx : |z.val 0|=1
        · change max |z.val 0| |(z.val 1+1)/2|=1
          have hj : 0≤(z.val 1+1)/2 := hJpos z
          rw [hx,abs_of_nonneg hj,max_eq_left]
          nlinarith [(abs_le.mp hb.2).2]
        · have hxlt : |z.val 0|<1 := lt_of_le_of_ne hb.1 hx
          have hyabs : |z.val 1|=1 := by
            apply le_antisymm hb.2
            by_contra hh
            have hlt := max_lt hxlt (lt_of_not_ge hh)
            rw [hm] at hlt
            exact lt_irrefl _ hlt
          have hy1 : z.val 1=1 := by
            rcases le_total 0 (z.val 1) with hs | hs
            · rwa [abs_of_nonneg hs] at hyabs
            · rw [abs_of_nonpos hs] at hyabs
              have heq : z.val 1= -1 := by linarith
              exact False.elim (hy heq)
          change max |z.val 0| |(z.val 1+1)/2|=1
          rw [hy1]
          norm_num only
          exact max_eq_right hb.1
  obtain ⟨F,hFfix,hFneg,hFboundary⟩ := boundary R hR B hB hBU hc hside
  let e : Q → Plane := F ∘ Subtype.val ∘ J
  let f : Q → Plane := B ∘ J
  have hei : IsEmbedding e := F.isEmbedding.comp (IsEmbedding.subtypeVal.comp hJe)
  have hfi : IsEmbedding f := hB.comp hJe
  have hag : ∀ z : Q,z.val ∈ modelCurve → e z=f z := by
    intro z hz
    rcases hJboundary z hz with hzero | hcurve
    · exact (hFneg (J z) hzero.le).trans (axisB (J z) hzero).symm
    · exact hFboundary (J z) hcurve (hJpos z)
  have hrange : Set.range e=Set.range f := sameRange e f hei hfi hag
  let A := Set.range e
  let E := hei.toHomeomorph
  let D := hfi.toHomeomorph
  let C : A ≃ₜ A := E.symm.trans (D.trans (Homeomorph.setCongr hrange.symm))
  have hC (z : Q) : (C (E z) : Plane)=f z := by
    change (D (E.symm (E z)) : Plane)=f z
    rw [E.symm_apply_apply]
    rfl
  have hclosed : IsClosed A := (isCompact_range hei.continuous).isClosed
  have hCfront (x : A) (hx : (x:Plane) ∈ frontier A) : (C x : Plane)=x := by
    as_aux_lemma =>
      have hh : (x:Plane) ∈ e '' {z : Q | (z:Plane) ∈ frontier Q} := by
        rw [embedded_compact_planar_region_frontier_probe Q (isCompact_closedSquare 0 1) e hei]
        exact hx
      obtain ⟨z,hz,hzx⟩ := hh
      have hxE : E z=x := Subtype.ext hzx
      rw [← hxE,hC]
      have hzm : z.val ∈ modelCurve := by rw [modelCurve_eq_frontier]; exact hz
      exact (hag z hzm).symm
  obtain ⟨K,hKcore,hKfix⟩ := patch A hclosed C hCfront
  have hposA : interior A ⊆ {z : Plane | 0<z 1} := by
    as_aux_lemma =>
      intro z hz
      have hz' : z ∈ interior (Set.range f) := hrange ▸ hz
      obtain ⟨q,hq⟩ := interior_subset hz'
      have hi := (embedded_planar_region_interior_iff_probe Q f hfi q).mp (hq.symm ▸ hz')
      rw [Plane.interior_closedSquare] at hi
      have hiR : max |q.val 0| |q.val 1|<1 := by simpa [Plane.openSquare,Plane.supDist,Plane.supNorm] using hi
      have hy : -1<q.val 1 := (abs_lt.mp (lt_of_le_of_lt (le_max_right _ _) hiR)).1
      have hJgt : 0<(J q).val 1 := by change 0<(q.val 1+1)/2; linarith
      have hh := hside (J q) hJgt
      change 0<f q 1 at hh
      rwa [hq] at hh
  have hAU : A ⊆ Plane.openSquare 0 R := by
    intro z hz
    have hz' : z ∈ Set.range f := hrange ▸ hz
    obtain ⟨q,rfl⟩ := hz'
    exact hBU (Set.mem_range_self (J q))
  let H : Plane ≃ₜ Plane := F.trans K
  have hHJ (q : Q) : H (J q)=B (J q) := by
    change K (e q)=f q
    have hh := hKcore (E q)
    exact hh.trans (hC q)
  refine ⟨H,?_,?_,?_⟩
  · intro z hz
    change K (F z)=z
    rw [hFfix z hz]
    apply hKfix
    intro hi
    exact hz (hAU (interior_subset hi))
  · intro z hz
    change K (F z)=z
    rw [hFneg z hz]
    apply hKfix
    intro hi
    exact not_lt_of_ge hz (hposA hi)
  · intro z hz
    let q : Q := ⟨Plane.mk (z.val 0) (2*z.val 1-1),by
      have hb := bounds z
      have hy : |2*z.val 1-1|≤1 := abs_le.mpr ⟨by linarith,by nlinarith [(abs_le.mp hb.2).2]⟩
      simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using max_le hb.1 hy⟩
    have hq : J q=z := by
      apply Subtype.ext
      apply PiLp.ext
      intro i
      fin_cases i
      · rfl
      · change ((2*z.val 1-1)+1)/2=z.val 1; ring
    have hh := hHJ q
    rwa [hq] at hh

private theorem outsideBandsPackaging_2506_oriented (R : ℝ) (hR : 1<R)
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hBU : Set.range B ⊆ Plane.openSquare 0 R)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hplus : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1)
    (hminus : ∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0) :
    ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
      (∀ t : ℝ,H (Plane.mk t 0)=Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),H z=B z := by
  have positive (R : ℝ) (hR : 1<R)
      (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hBU : Set.range B ⊆ Plane.openSquare 0 R)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hside : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) :
      ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
        (∀ z, z 1≤0 → H z=z) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 1 → H z=B z := by
    apply outsideBandsPackaging_2517_positive <;> assumption
  classical
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let Y : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0) (-z 1)
    invFun := fun z => Plane.mk (z 0) (-z 1)
    left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  have hYY (z : Plane) : Y (Y z)=z := Y.symm_apply_apply z
  have hYopen (z : Plane) : Y z ∈ Plane.openSquare 0 R ↔ z ∈ Plane.openSquare 0 R := by
    simp [Y,Plane.openSquare,Plane.supDist,Plane.supNorm,Plane.mk]
  let T : Q → Q := fun z => ⟨Y z,by simpa [Y,Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk] using z.property⟩
  have hTc : Continuous T := (Y.continuous.comp continuous_subtype_val).subtype_mk _
  have hTi : Function.Injective T := by
    intro z w he
    apply Subtype.ext
    exact Y.injective (congrArg Subtype.val he)
  have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
  have hTT (z : Q) : T (T z)=z := Subtype.ext (hYY z)
  have hTaxis (t : Icc (-1 : ℝ) 1) :
      T ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
      ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
    apply Subtype.ext
    simp [T,Y,Plane.mk]
  let M : Q → Plane := Y ∘ B ∘ T
  have hM : IsEmbedding M := Y.isEmbedding.comp (hB.comp hTe)
  have hMU : Set.range M ⊆ Plane.openSquare 0 R := by
    rintro z ⟨q,rfl⟩
    exact (hYopen (B (T q))).mpr (hBU (Set.mem_range_self _))
  have hMc (t : Icc (-1 : ℝ) 1) :
      M ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0 := by
    change Y (B (T _))=Plane.mk t 0
    rw [hTaxis,hc]
    simp [Y,Plane.mk]
  have hMp (z : Q) (hz : 0<z.val 1) : 0<M z 1 := by
    have hn : (T z).val 1<0 := by change -z.val 1<0; linarith
    have hh := hminus (T z) hn
    change 0< -(B (T z) 1)
    linarith
  obtain ⟨P,hPfix,hPneg,hPcore⟩ := positive R hR B hB hBU hc hplus
  obtain ⟨N,hNfix,hNneg,hNcore⟩ := positive R hR M hM hMU hMc hMp
  let F : Plane ≃ₜ Plane := (Y.trans N).trans Y
  have hFfix (z : Plane) (hz : z ∉ Plane.openSquare 0 R) : F z=z := by
    change Y (N (Y z))=z
    have hy : Y z ∉ Plane.openSquare 0 R := fun h => hz ((hYopen z).mp h)
    rw [hNfix _ hy,hYY]
  have hFpos (z : Plane) (hz : 0≤z 1) : F z=z := by
    change Y (N (Y z))=z
    have hy : (Y z) 1≤0 := by change -z 1≤0; linarith
    rw [hNneg _ hy,hYY]
  have hFcore (z : Q) (hz : z.val 1≤0) : F z=B z := by
    change Y (N (T z).val)=B z
    have hy : 0≤(T z).val 1 := by change 0≤ -z.val 1; linarith
    rw [hNcore (T z) hy]
    change Y (Y (B (T (T z))))=B z
    rw [hTT,hYY]
  let H : Plane ≃ₜ Plane := P.trans F
  refine ⟨H,?_,?_,?_⟩
  · intro z hz
    change F (P z)=z
    rw [hPfix _ hz,hFfix _ hz]
  · intro t
    change F (P (Plane.mk t 0))=Plane.mk t 0
    rw [hPneg _ (by simp [Plane.mk]),hFpos _ (by simp [Plane.mk])]
  · intro z
    change F (P z.val)=B z
    rcases le_or_gt (z.val 1) 0 with hn | hp
    · rw [hPneg _ hn,hFcore z hn]
    · rw [hPcore z hp.le,hFpos _ (hplus z hp).le]

private theorem outsideBandsPackaging_2343_supported (R : ℝ) (hR : 1 < R)
    (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hBU : Set.range B ⊆ Plane.openSquare 0 R)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by
        simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 R → H z = z) ∧
      (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) = B z := by
  have recognize (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1=0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∀ z, B z 1 = 0 ↔ z.val 1 = 0 := by
    apply outsideBandsPackaging_2356_recognize <;> assumption
  have sides (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (haxis : ∀ z, B z 1=0 ↔ z.val 1=0)
      (hB0 : B ⟨0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩ = 0) :
      ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1) ∧
        (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0)) ∨
      ((∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → B z 1<0) ∧
        (∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → 0<B z 1)) := by
    apply outsideBandsPackaging_2383_sides <;> assumption
  have oriented (R : ℝ) (hR : 1<R)
      (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hBU : Set.range B ⊆ Plane.openSquare 0 R)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hplus : ∀ z : ↥(Plane.closedSquare 0 1),0<z.val 1 → 0<B z 1)
      (hminus : ∀ z : ↥(Plane.closedSquare 0 1),z.val 1<0 → B z 1<0) :
      ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 R → H z=z) ∧
        (∀ t : ℝ,H (Plane.mk t 0)=Plane.mk t 0) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),H z=B z := by
    apply outsideBandsPackaging_2506_oriented <;> assumption
  classical
  let Q := Plane.closedSquare 0 1
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
  let Y : Plane ≃ₜ Plane := {
    toFun := fun z => Plane.mk (z 0) (-z 1)
    invFun := fun z => Plane.mk (z 0) (-z 1)
    left_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    right_inv := by intro z; apply PiLp.ext; intro i; fin_cases i <;> simp [Plane.mk]
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop
  }
  have hYY (z : Plane) : Y (Y z)=z := Y.symm_apply_apply z
  let T : Q → Q := fun z => ⟨Y z,by simpa [Y,Q,Plane.closedSquare,Plane.supDist,Plane.supNorm,Plane.mk] using z.property⟩
  have hTc : Continuous T := (Y.continuous.comp continuous_subtype_val).subtype_mk _
  have hTi : Function.Injective T := by
    intro z w he
    apply Subtype.ext
    exact Y.injective (congrArg Subtype.val he)
  have hTe : IsEmbedding T := (hTc.isClosedEmbedding hTi).isEmbedding
  have hTT (z : Q) : T (T z)=z := Subtype.ext (hYY z)
  have hTaxis (t : Icc (-1 : ℝ) 1) :
      T ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ =
      ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ := by
    apply Subtype.ext
    simp [T,Y,Plane.mk]
  have haxis := recognize B hB hc hmeet
  have hB0 : B ⟨0,by simp [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩=0 := by
    have hh := hc ⟨0,by norm_num⟩
    have hz : Plane.mk 0 0=(0:Plane) := by apply PiLp.ext; intro i; fin_cases i <;> rfl
    simpa only [hz] using hh
  rcases sides B hB haxis hB0 with ⟨hp,hn⟩ | ⟨hp,hn⟩
  · obtain ⟨H,hHfix,hHaxis,hHcore⟩ := oriented R hR B hB hBU hc hp hn
    refine ⟨false,H,hHfix,hHaxis,?_⟩
    intro z
    have hz : Plane.mk (z.val 0) (z.val 1)=z.val := by
      apply PiLp.ext
      intro i
      fin_cases i <;> rfl
    change H (Plane.mk (z.val 0) (z.val 1))=B z
    rw [hz,hHcore]
  · let C : Q → Plane := B ∘ T
    have hC : IsEmbedding C := hB.comp hTe
    have hCU : Set.range C ⊆ Plane.openSquare 0 R := by
      rintro z ⟨q,rfl⟩
      exact hBU (Set.mem_range_self (T q))
    have hCc (t : Icc (-1 : ℝ) 1) :
        C ⟨Plane.mk t 0,by simpa [Q,Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0 := by
      change B (T _)=Plane.mk t 0
      rw [hTaxis,hc]
    have hCp (z : Q) (hz : 0<z.val 1) : 0<C z 1 := by
      have ht : (T z).val 1<0 := by change -z.val 1<0; linarith
      exact hn (T z) ht
    have hCn (z : Q) (hz : z.val 1<0) : C z 1<0 := by
      have ht : 0<(T z).val 1 := by change 0< -z.val 1; linarith
      exact hp (T z) ht
    obtain ⟨H,hHfix,hHaxis,hHcore⟩ := oriented R hR C hC hCU hCc hCp hCn
    refine ⟨true,H,hHfix,hHaxis,?_⟩
    intro z
    change H (T z).val=B z
    rw [hHcore]
    change B (T (T z))=B z
    rw [hTT]

private theorem outsideBandsPackaging_2226_straighten (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
    (hc : ∀ t : Icc (-1 : ℝ) 1,
      B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
    (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
      (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
    ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 2 → H z = z) ∧
      (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1),
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
          B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
            have hz : max |z.val 0| |z.val 1| ≤ 1 := by
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
            have hx := (le_max_left _ _).trans hz
            have hy := (le_max_right _ _).trans hz
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
              max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
  have bounded (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
        ∃ C : ↥(Plane.closedSquare 0 1) → Plane, IsEmbedding C ∧
          Set.range C ⊆ Plane.openSquare 0 2 ∧
          (∀ t : Icc (-1 : ℝ) 1,
            C ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0) ∧
          (Set.range C ∩ {z : Plane | z 1 = 0} =
            (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) ∧
          ∀ z, C z = B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
            have hz : max |z.val 0| |z.val 1| ≤ 1 := by
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
            have hx := (le_max_left _ _).trans hz
            have hy := (le_max_right _ _).trans hz
            simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
              max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
    apply outsideBandsPackaging_2244_bounded <;> assumption
  have supported (R : ℝ) (hR : 1 < R)
      (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hBU : Set.range B ⊆ Plane.openSquare 0 R)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by
          simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 R → H z = z) ∧
        (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),
          H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) = B z := by
    apply outsideBandsPackaging_2343_supported <;> assumption
  obtain ⟨δ,hδ,C,hC,hCU,hCc,hCmeet,hCformula⟩ := bounded B hB hc hmeet
  obtain ⟨flip,H,hfix,haxis,hformula⟩ := supported 2 (by norm_num) C hC hCU hCc hCmeet
  exact ⟨δ,hδ,flip,H,hfix,haxis,fun z => (hformula z).trans (hCformula z)⟩

private theorem outsideBandsPackaging_360_advance {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m n : I) (hm0 : 0 < m) (hmn : m < n)
    (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
    (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
    (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
    (e : OpenPartialHomeomorph S Plane) (hps : p '' Icc m n ⊆ e.source)
    (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m n ⊆ U)
    (k : ℝ) (hk : 0 < k ∧ k < 1) :
    let M : I := ⟨(m : ℝ)+((n : ℝ)-m)*k,by
      constructor
      · nlinarith [m.property.1,show (m : ℝ)<n from hmn]
      · have hb := mul_le_mul_of_nonneg_left hk.2.le (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
        nlinarith [n.property.2]⟩
    ∃ G : I × Icc (-1 : ℝ) 1 → S,
      IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
      (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend ((M : ℝ)*t)) ∧
      Set.range G ∩ Set.range p = p '' Icc 0 M ∧
      Set.range G ⊆ Set.range E ∪ U := by
  have terminal (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (U : Set S) (hU : IsOpen U) (hport : E (1,⟨0,by norm_num⟩) ∈ U) :
      ∃ d : ℝ, ∃ hd : 0 < d ∧ d < 1,
        ∃ B : I × Icc (-1 : ℝ) 1 → S,
          IsEmbedding B ∧ Set.range B ⊆ U ∧
          (∀ z : I × Icc (-1 : ℝ) 1,
            B z = E (⟨1-d+d*z.1,by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2]⟩,
              ⟨d*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2]⟩)) := by
    as_aux_lemma =>
      let R := ↥I × ↥(Icc (-1 : ℝ) 1)
      let O : Set R := E ⁻¹' U
      have hO : IsOpen O := hU.preimage hE.continuous
      have hz : (1,⟨0,by norm_num⟩) ∈ O := hport
      obtain ⟨e,he,heO⟩ := Metric.mem_nhds_iff.mp (hO.mem_nhds hz)
      let d := min (e/2) (1/2 : ℝ)
      have hd : 0 < d ∧ d < 1 := by
        constructor
        · dsimp [d]; positivity
        · have hh := min_le_right (e/2) (1/2 : ℝ); dsimp [d]; linarith
      have hde : d < e := by have hh := min_le_left (e/2) (1/2 : ℝ); dsimp [d]; linarith
      let k : R → R := fun z =>
        (⟨1-d+d*z.1,by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hd.1,hd.2]⟩,
         ⟨d*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hd.1,hd.2]⟩)
      have hkc : Continuous k := by dsimp [k,R]; fun_prop
      have hki : Function.Injective k := by
        as_aux_lemma =>
          intro z w heq
          have h0 := congrArg (fun v : R => (v.1 : ℝ)) heq
          have h1 := congrArg (fun v : R => (v.2 : ℝ)) heq
          apply Prod.ext <;> apply Subtype.ext
          · change 1-d+d*(z.1 : ℝ) = 1-d+d*(w.1 : ℝ) at h0
            nlinarith [hd.1]
          · exact mul_left_cancel₀ hd.1.ne' h1
      have hke : IsEmbedding k := (hkc.isClosedEmbedding hki).isEmbedding
      let B := E ∘ k
      have hB : IsEmbedding B := hE.comp hke
      have hBU : Set.range B ⊆ U := by
        as_aux_lemma =>
          rintro y ⟨z,rfl⟩
          apply heO
          rw [Metric.mem_ball,Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
          change max |1-d+d*(z.1 : ℝ)-1| |d*(z.2 : ℝ)-0| < e
          apply max_lt
          · apply abs_lt.mpr
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hd.1,hde]
          · apply abs_lt.mpr
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hd.1,hde]
      exact ⟨d,hd,B,hB,hBU,fun z => rfl⟩
  have square_extension (e : OpenPartialHomeomorph S Plane)
      (B : I × Icc (-1 : ℝ) 1 → S) (hB : IsEmbedding B)
      (hBs : Set.range B ⊆ e.source) :
      ∃ H : Plane ≃ₜ Plane,
        ∀ z : I × Icc (-1 : ℝ) 1,
          H (Plane.mk (-1+2*z.1) z.2) = e (B z) := by
    as_aux_lemma =>
      classical
      let Q := Plane.closedSquare 0 1
      let R := ↥I × ↥(Icc (-1 : ℝ) 1)
      have hbounds (v : ↥Q) :
          -1 ≤ (v : Plane) 0 ∧ (v : Plane) 0 ≤ 1 ∧
          -1 ≤ (v : Plane) 1 ∧ (v : Plane) 1 ≤ 1 := by
        have hv := mem_closedSquare_zero_one.mp v.property
        change max |(v : Plane) 0| |(v : Plane) 1| ≤ 1 at hv
        have h0 := abs_le.mp ((le_max_left _ _).trans hv)
        have h1 := abs_le.mp ((le_max_right _ _).trans hv)
        exact ⟨h0.1,h0.2,h1.1,h1.2⟩
      let q : ↥Q → R := fun v =>
        (⟨((v : Plane) 0+1)/2,by constructor <;> linarith [(hbounds v).1,(hbounds v).2.1]⟩,
         ⟨(v : Plane) 1,⟨(hbounds v).2.2.1,(hbounds v).2.2.2⟩⟩)
      have hqc : Continuous q := by dsimp [q,R]; fun_prop
      have hqi : Function.Injective q := by
        as_aux_lemma =>
          intro v w hh
          have h0 := congrArg (fun z : R => (z.1 : ℝ)) hh
          have h1 := congrArg (fun z : R => (z.2 : ℝ)) hh
          apply Subtype.ext
          ext i
          fin_cases i
          · change (v : Plane) 0 = (w : Plane) 0
            change ((v : Plane) 0+1)/2 = ((w : Plane) 0+1)/2 at h0
            linarith
          · exact h1
      let b : ↥Q → Plane := e ∘ B ∘ q
      have hbc : Continuous b := by
        apply continuousOn_univ.mp
        apply e.continuousOn.comp (hB.continuous.comp hqc).continuousOn
        intro v _
        exact hBs (Set.mem_range_self _)
      have hbi : Function.Injective b := by
        intro v w hh
        exact hqi (hB.injective (e.injOn (hBs (Set.mem_range_self _))
          (hBs (Set.mem_range_self _)) hh))
      letI : CompactSpace ↥Q := isCompact_iff_compactSpace.mp (isCompact_closedSquare 0 1)
      have hbe : IsEmbedding b := (hbc.isClosedEmbedding hbi).isEmbedding
      obtain ⟨H,hH⟩ := exists_ambient_extension_of_embedded_closed_square b hbe
      refine ⟨H,?_⟩
      intro z
      have hzQ : Plane.mk (-1+2*z.1) z.2 ∈ Q := by
        rw [mem_closedSquare_zero_one]
        change max |(-1+2*(z.1 : ℝ))| |(z.2 : ℝ)| ≤ 1
        exact max_le (abs_le.mpr ⟨by linarith [z.1.property.1],by linarith [z.1.property.2]⟩)
          (abs_le.mpr z.2.property)
      have hqz : q ⟨Plane.mk (-1+2*z.1) z.2,hzQ⟩ = z := by
        apply Prod.ext <;> apply Subtype.ext
        · change (-1+2*(z.1 : ℝ)+1)/2 = (z.1 : ℝ)
          ring
        · rfl
      have hh := hH ⟨Plane.mk (-1+2*z.1) z.2,hzQ⟩
      change H (Plane.mk (-1+2*z.1) z.2) = e (B (q _)) at hh
      rw [hqz] at hh
      exact hh
  have remote (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (d : ℝ) (hd : 0 < d ∧ d < 1)
      (B : I × Icc (-1 : ℝ) 1 → S)
      (hB : ∀ z : I × Icc (-1 : ℝ) 1,
        B z = E (⟨1-d+d*z.1,by constructor <;> nlinarith [z.1.property.1,z.1.property.2]⟩,
          ⟨d*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2]⟩))
      (U : Set S) (hU : IsOpen U) (hport : E (1,⟨0,by norm_num⟩) ∈ U) :
      ∃ V : Set S, IsOpen V ∧ E (1,⟨0,by norm_num⟩) ∈ V ∧ V ⊆ U ∧
        Set.range E ∩ V ⊆ Set.range B := by
    as_aux_lemma =>
      have locality
          (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
          (a b : ℝ) (ha : a < 1) (hb : 0 < b)
          (U : Set S) (hU : IsOpen U)
          (hport : E (1,⟨0,by norm_num⟩) ∈ U) :
          ∃ V : Set S, IsOpen V ∧ E (1,⟨0,by norm_num⟩) ∈ V ∧ V ⊆ U ∧
            ∀ z : I × Icc (-1 : ℝ) 1, E z ∈ V → a < (z.1 : ℝ) ∧ |(z.2 : ℝ)| < b := by
        as_aux_lemma =>
          let K : Set (I × Icc (-1 : ℝ) 1) :=
            {z | (z.1 : ℝ) ≤ a ∨ b ≤ |(z.2 : ℝ)|}
          have hK : IsClosed K := by
            exact (isClosed_le (show Continuous (fun z : I × Icc (-1 : ℝ) 1 =>
              (z.1 : ℝ)) from by fun_prop) (continuous_const (y := a))).union
              (isClosed_le (continuous_const (y := b))
                (show Continuous (fun z : I × Icc (-1 : ℝ) 1 => |(z.2 : ℝ)|) from by fun_prop))
          have hEK : IsClosed (E '' K) := (hK.isCompact.image hE.continuous).isClosed
          have hnot : E (1,⟨0,by norm_num⟩) ∉ E '' K := by
            as_aux_lemma =>
              rintro ⟨z,hz,he⟩
              have hzEq : z = (1,⟨0,by norm_num⟩) := hE.injective he
              subst z
              rcases hz with hz | hz
              · exact (not_le_of_gt ha) hz
              · simp only [abs_zero] at hz
                exact (not_le_of_gt hb) hz
          refine ⟨U \ E '' K,hU.sdiff hEK,⟨hport,hnot⟩,sdiff_subset,?_⟩
          intro z hz
          have hn : z ∉ K := fun hk => hz.2 ⟨z,hk,rfl⟩
          change ¬ ((z.1 : ℝ) ≤ a ∨ b ≤ |(z.2 : ℝ)|) at hn
          exact ⟨lt_of_not_ge (fun h => hn (Or.inl h)),
            lt_of_not_ge (fun h => hn (Or.inr h))⟩
                      
      obtain ⟨V,hV,hportV,hVU,hlocal⟩ := locality E hE (1-d) d
        (by linarith [hd.1]) hd.1 U hU hport
      refine ⟨V,hV,hportV,hVU,?_⟩
      rintro y ⟨⟨z,rfl⟩,hzV⟩
      obtain ⟨ht,hw⟩ := hlocal z hzV
      let t : I := ⟨((z.1 : ℝ)-1+d)/d,by
        constructor
        · apply div_nonneg
          · linarith
          · exact hd.1.le
        · apply (div_le_one hd.1).mpr
          linarith [z.1.property.2]⟩
      let w : Icc (-1 : ℝ) 1 := ⟨(z.2 : ℝ)/d,by
        have hw' := abs_lt.mp hw
        constructor
        · apply (le_div_iff₀ hd.1).mpr
          linarith
        · apply (div_le_iff₀ hd.1).mpr
          linarith⟩
      refine ⟨(t,w),?_⟩
      rw [hB]
      congr 1
      apply Prod.ext <;> apply Subtype.ext
      · change 1-d+d*(t : ℝ) = (z.1 : ℝ)
        dsimp [t]
        field_simp [hd.1.ne']
        <;> ring
      · change d*(w : ℝ) = (z.2 : ℝ)
        dsimp [w]
        field_simp [hd.1.ne']
  have whole_future {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m n : I) (hmn : m < n)
      (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
      (B : I × Icc (-1 : ℝ) 1 → S)
      (hBE : Set.range B ⊆ Set.range E)
      (e : OpenPartialHomeomorph S Plane) (hBs : Set.range B ⊆ e.source)
      (hport : B (1,⟨0,by norm_num⟩) = p m)
      (hps : p '' Icc m n ⊆ e.source)
      (H : Plane ≃ₜ Plane)
      (hH : ∀ z : I × Icc (-1 : ℝ) 1, H (Plane.mk (-1+2*z.1) z.2) = e (B z))
      (U V : Set S) (hU : IsOpen U) (hV : IsOpen V) (hmV : p m ∈ V)
      (hpU : p '' Icc m n ⊆ U)
      (hEV : Set.range E ∩ V ⊆ Set.range B) :
      ∃ rho : ℝ, ∃ hrho : 0 < rho ∧ rho ≤ 1,
        ∃ P : I × Icc (-1 : ℝ) 1 → S,
          IsEmbedding P ∧ Set.range P ⊆ U ∧
          (∀ w : Icc (-1 : ℝ) 1, P (0,w) = B (1,⟨rho*w,by constructor <;> nlinarith [w.property.1,w.property.2,hrho.1,hrho.2]⟩)) ∧
          (∀ t : I, P (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+((n : ℝ)-m)*t)) ∧
          Set.range P ∩ Set.range E = Set.range (fun w : Icc (-1 : ℝ) 1 => P (0,w)) := by
    apply outsideBandsPackaging_554_whole_future <;> assumption
  have narrow {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m : I) (h : ℝ) (hh : 0 < h ∧ (m : ℝ)+h ≤ 1)
      (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+h*t))
      (hpre : Set.range E ∩ p '' Icc 0 m = {p m})
      (k : ℝ) (hk : 0 < k ∧ k < 1) :
      ∃ lambda : ℝ, ∃ hl : 0 < lambda ∧ lambda ≤ 1,
        ∃ R : I × Icc (-1 : ℝ) 1 → S,
          (∀ z : I × Icc (-1 : ℝ) 1, R z = E
            (⟨k*z.1,by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hk.1,hk.2]⟩,
             ⟨lambda*z.2,by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hl.1,hl.2]⟩)) ∧
          IsEmbedding R ∧ Set.range R ⊆ Set.range E ∧
          (∀ w : Icc (-1 : ℝ) 1, R (0,w) = E (0,⟨lambda*w,by
            constructor <;> nlinarith [w.property.1,w.property.2,hl.1,hl.2]⟩)) ∧
          (∀ t : I, R (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+(h*k)*t)) ∧
          Set.range R ∩ Set.range p = p '' Icc m
            ⟨(m : ℝ)+h*k,by constructor <;> nlinarith [m.property.1]⟩ := by
    apply outsideBandsPackaging_767_narrow <;> assumption
  have paste_prefix {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m : I) (hm0 : 0 < m) (hm1 : m < 1)
      (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
      (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
      (h : ℝ) (hh : 0 < h ∧ (m : ℝ)+h < 1)
      (lambda : ℝ) (hlambda : 0 < lambda ∧ lambda ≤ 1)
      (R : I × Icc (-1 : ℝ) 1 → S) (hR : IsEmbedding R)
      (hRport : ∀ w : Icc (-1 : ℝ) 1, R (0,w) = E (1,⟨lambda*w,by constructor <;> nlinarith [w.property.1,w.property.2,hlambda.1,hlambda.2]⟩))
      (hRc : ∀ t : I, R (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)+h*t))
      (hRE : Set.range R ∩ Set.range E = Set.range (fun w : Icc (-1 : ℝ) 1 => R (0,w)))
      (hRmeet : Set.range R ∩ Set.range p = p '' Icc m ⟨(m : ℝ)+h,by constructor <;> linarith [m.property.1,hh.1]⟩)
      (U : Set S) (hRU : Set.range R ⊆ U) :
      ∃ G : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
        (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend (((m : ℝ)+h)*t)) ∧
        Set.range G ∩ Set.range p = p '' Icc 0 ⟨(m : ℝ)+h,by constructor <;> linarith [m.property.1,hh.1]⟩ ∧
        Set.range G ⊆ Set.range E ∪ U := by
    apply outsideBandsPackaging_903_paste_prefix <;> assumption
  classical
  dsimp only
  have hmnR : (m : ℝ) < n := hmn
  have hmR : 0 < (m : ℝ) := hm0
  have hnm : 0 < (n : ℝ)-m := sub_pos.mpr hmnR
  have hM0 : 0 ≤ (m : ℝ)+((n : ℝ)-m)*k := by nlinarith [m.property.1]
  have hMn : (m : ℝ)+((n : ℝ)-m)*k < n := by nlinarith
  have hM1 : (m : ℝ)+((n : ℝ)-m)*k < 1 := hMn.trans_le n.property.2
  have hport : E (1,⟨0,by norm_num⟩) = p m := by
    rw [hcenter]
    norm_num
  have hmI : m ∈ Icc m n := ⟨le_rfl,hmn.le⟩
  let U0 := U ∩ e.source
  have hU0 : IsOpen U0 := hU.inter e.open_source
  have hmU0 : E (1,⟨0,by norm_num⟩) ∈ U0 := by rw [hport]; exact ⟨hpU ⟨m,hmI,rfl⟩,hps ⟨m,hmI,rfl⟩⟩
  obtain ⟨d,hd,B,hB,hBU,hBformula⟩ := terminal E hE U0 hU0 hmU0
  have hBE : Set.range B ⊆ Set.range E := by
    rintro q ⟨z,rfl⟩
    exact ⟨_,(hBformula z).symm⟩
  have hBs : Set.range B ⊆ e.source := fun q hq => (hBU hq).2
  have hBport : B (1,⟨0,by norm_num⟩) = p m := by
    rw [hBformula,← hport]
    apply congrArg E
    apply Prod.ext <;> apply Subtype.ext
    · dsimp; ring
    · dsimp; ring
  obtain ⟨H,hH⟩ := square_extension e B hB hBs
  obtain ⟨V,hV,hmV,hVU,hEV⟩ := remote E hE d hd B hBformula U0 hU0 hmU0
  have hmV' : p m ∈ V := hport ▸ hmV
  obtain ⟨rho,hrho,P,hP,hPU,hP0,hPc,hPE⟩ := whole_future p hp m n hmn E hE hmeet B hBE e hBs hBport hps H hH U V hU hV hmV' hpU hEV
  have hwidthpos : 0 < d*rho := mul_pos hd.1 hrho.1
  have hwidthle : d*rho ≤ 1 := by
    have hb := mul_le_mul_of_nonneg_left hrho.2 hd.1.le
    nlinarith [hd.2]
  have hwidth (w : Icc (-1 : ℝ) 1) : -1 ≤ d*rho*w ∧ d*rho*w ≤ 1 := by
    have hb0 := mul_le_mul_of_nonneg_left w.property.1 hwidthpos.le
    have hb1 := mul_le_mul_of_nonneg_left w.property.2 hwidthpos.le
    constructor <;> nlinarith
  have hPport (w : Icc (-1 : ℝ) 1) : P (0,w) =
      E (1,⟨d*rho*w,hwidth w⟩) := by
    rw [hP0,hBformula]
    apply congrArg E
    apply Prod.ext
    · apply Subtype.ext; simp
    · apply Subtype.ext; ring
  have hpre : Set.range P ∩ p '' Icc 0 m = {p m} := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨hqP,⟨s,hs,rfl⟩⟩
        have hsE : p s ∈ Set.range E := by
          have hh' : p s ∈ Set.range E ∩ Set.range p := hmeet ▸ ⟨s,hs,rfl⟩
          exact hh'.1
        obtain ⟨w,hw⟩ := hPE ▸ (show p s ∈ Set.range P ∩ Set.range E from ⟨hqP,hsE⟩)
        let t : I := ⟨(s : ℝ)/m,⟨div_nonneg s.property.1 hmR.le,(div_le_one hmR).mpr (show (s : ℝ) ≤ m from hs.2)⟩⟩
        have ht : (m : ℝ)*t = s := mul_div_cancel₀ _ hmR.ne'
        have hEt : E (t,⟨0,by norm_num⟩) = p s := by rw [hcenter,ht,p.extend_apply s.property]
        have he := hE.injective (hEt.trans (hw.symm.trans (hPport w)))
        have heR := congrArg (fun z : I × Icc (-1 : ℝ) 1 => (z.1 : ℝ)) he
        have hsEq : s = m := by
          apply Subtype.ext
          change (s : ℝ)/m=1 at heR
          exact (div_eq_one_iff_eq hmR.ne').mp heR
        rw [hsEq]
        exact Set.mem_singleton _
      · intro hq
        have he : q = p m := hq
        rw [he]
        refine ⟨⟨(0,⟨0,by norm_num⟩),?_⟩,⟨m,⟨m.property.1,le_rfl⟩,rfl⟩⟩
        rw [hPc]
        norm_num
  have hh : 0 < (n : ℝ)-m ∧ (m : ℝ)+((n : ℝ)-m) ≤ 1 := ⟨hnm,by linarith [n.property.2]⟩
  obtain ⟨lambda,hl,R,hRformula,hR,hRP,hR0,hRc,hRmeet⟩ := narrow p hp m ((n : ℝ)-m) hh P hP hPc hpre k hk
  let total := d*rho*lambda
  have htpos : 0 < total := mul_pos (mul_pos hd.1 hrho.1) hl.1
  have htle : total ≤ 1 := by
    have h1 := mul_le_mul_of_nonneg_left hrho.2 hd.1.le
    have h2 := mul_le_mul_of_nonneg_left hl.2 (mul_pos hd.1 hrho.1).le
    dsimp [total]
    nlinarith [hd.2]
  have hRport (w : Icc (-1 : ℝ) 1) : R (0,w) = E (1,⟨total*w,by constructor <;> nlinarith [w.property.1,w.property.2,htpos,htle]⟩) := by
    as_aux_lemma =>
      rw [hR0,hPport]
      apply congrArg E
      apply Prod.ext
      · rfl
      · apply Subtype.ext
        dsimp [total]
        ring
  have hRE : Set.range R ∩ Set.range E = Set.range (fun w : Icc (-1 : ℝ) 1 => R (0,w)) := by
    as_aux_lemma =>
      ext q
      constructor
      · rintro ⟨⟨z,rfl⟩,hqE⟩
        obtain ⟨w,hw⟩ := hPE ▸ (show R z ∈ Set.range P ∩ Set.range E from ⟨hRP (Set.mem_range_self _),hqE⟩)
        have he := hP.injective ((hRformula z).symm.trans hw.symm)
        have heR := congrArg (fun z : I × Icc (-1 : ℝ) 1 => (z.1 : ℝ)) he
        have hz0 : z.1 = 0 := by
          apply Subtype.ext
          change k*(z.1 : ℝ)=0 at heR
          exact (mul_eq_zero.mp heR).resolve_left hk.1.ne'
        refine ⟨z.2,?_⟩
        have hez : z = (0,z.2) := Prod.ext hz0 rfl
        rw [hez]
      · rintro ⟨w,rfl⟩
        refine ⟨Set.mem_range_self _,?_⟩
        exact ⟨_,(hRport w).symm⟩
  have hadv : 0 < ((n : ℝ)-m)*k ∧ (m : ℝ)+((n : ℝ)-m)*k < 1 := ⟨mul_pos hnm hk.1,hM1⟩
  have hm1 : m < 1 := hmn.trans_le n.property.2
  obtain ⟨G,hG,hG0,hGc,hGmeet,hGU⟩ := paste_prefix p hp m hm0 hm1 E hE hcenter hmeet (((n : ℝ)-m)*k) hadv total ⟨htpos,htle⟩ R hR hRport hRc hRE hRmeet U (hRP.trans hPU)
  exact ⟨G,hG,hG0,hGc,hGmeet,hGU⟩

private theorem outsideBandsPackaging_2090_straighten (C : I × BandWidth → Plane) (hC : IsEmbedding C)
    (height : I → ℝ) (hh : Continuous height) (hm : StrictMono height)
    (hc : ∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
    (haxis : ∀ z, C z 1=0 ↔ (z.2:ℝ)=0) :
    ∃ A : I ≃ₜ I,
      (∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) ∧
    ∃ width : ℝ, 0 < width ∧ width ≤ 1 ∧
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 2 → H z=z) ∧
      (∀ x : ℝ,H (Plane.mk x 0)=Plane.mk x 0) ∧
      ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
          Plane.mk ((2*(C (A t,w) 0-height 0))/(height 1-height 0)-1)
            (C (A t,w) 1) := by
  have normalize (C : I × Icc (-1 : ℝ) 1 → Plane) (hC : IsEmbedding C)
      (height : I → ℝ) (hh : Continuous height) (hm : StrictMono height)
      (hc : ∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
      (haxis : ∀ z, C z 1=0 ↔ (z.2:ℝ)=0) :
      ∃ B : ↥(Plane.closedSquare 0 1) → Plane, IsEmbedding B ∧
        (∀ t : Icc (-1 : ℝ) 1,
          B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩=Plane.mk t 0) ∧
        (Set.range B ∩ {z : Plane | z 1=0} =
          (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) ∧
        ∃ A : I ≃ₜ I,
          (∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) ∧
          ∀ z : ↥(Plane.closedSquare 0 1),
            B z=Plane.mk
              ((2*(C (A ⟨(z.val 0+1)/2,by
                  have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
                  constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩,
                  ⟨z.val 1,abs_le.mp ((le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property))⟩) 0-height 0))/(height 1-height 0)-1)
              (C (A ⟨(z.val 0+1)/2,by
                  have hx : |z.val 0|≤1 := (le_max_left _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property)
                  constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩,
                  ⟨z.val 1,abs_le.mp ((le_max_right _ _).trans (show max |z.val 0| |z.val 1|≤1 from by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property))⟩) 1) := by
    apply outsideBandsPackaging_2105_normalize <;> assumption
  have straighten (B : ↥(Plane.closedSquare 0 1) → Plane) (hB : IsEmbedding B)
      (hc : ∀ t : Icc (-1 : ℝ) 1,
        B ⟨Plane.mk t 0,by simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using abs_le.mpr t.property⟩ = Plane.mk t 0)
      (hmeet : Set.range B ∩ {z : Plane | z 1 = 0} =
        (fun t : Icc (-1 : ℝ) 1 => Plane.mk t 0) '' univ) :
      ∃ δ : ℝ, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 2 → H z = z) ∧
        (∀ t : ℝ, H (Plane.mk t 0) = Plane.mk t 0) ∧
        ∀ z : ↥(Plane.closedSquare 0 1),
          H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
            B ⟨Plane.mk (z.val 0) (δ*z.val 1),by
              have hz : max |z.val 0| |z.val 1| ≤ 1 := by
                simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
              have hx := (le_max_left _ _).trans hz
              have hy := (le_max_right _ _).trans hz
              simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm,abs_mul,abs_of_pos hδ.1] using
                max_le hx ((mul_le_mul_of_nonneg_left hy hδ.1.le).trans (by simpa using hδ.2))⟩ := by
    apply outsideBandsPackaging_2226_straighten <;> assumption
  obtain ⟨B,hB,hBc,hBaxis,A,hA,hformula⟩ := normalize C hC height hh hm hc haxis
  obtain ⟨width,hwidth,flip,H,hfix,hHx,hH⟩ := straighten B hB hBc hBaxis
  refine ⟨A,hA,width,hwidth.1,hwidth.2,flip,H,hfix,hHx,?_⟩
  intro z
  have hz : max |z.val 0| |z.val 1|≤1 := by
    simpa [Plane.closedSquare,Plane.supDist,Plane.supNorm] using z.property
  have hx := (le_max_left _ _).trans hz
  have hy := (le_max_right _ _).trans hz
  let t : I := ⟨(z.val 0+1)/2,by constructor <;> linarith [(abs_le.mp hx).1,(abs_le.mp hx).2]⟩
  let w : BandWidth := ⟨width*z.val 1,by
    have hw : |width*z.val 1|≤1 := by
      rw [abs_mul,abs_of_pos hwidth.1]
      exact (mul_le_mul_of_nonneg_left hy hwidth.1.le).trans (by simpa using hwidth.2)
    exact abs_le.mp hw⟩
  refine ⟨t,w,rfl,rfl,?_⟩
  rw [hH,hformula]
  rfl

private theorem outsideBandsPackaging_349_iterate {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S] {x y : S} (p : Path x y) (hp : IsEmbedding p)
    (m M : I) (hm0 : 0 < m) (hmM : m ≤ M) (hM1 : M < 1)
    (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
    (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
    (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
    (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m M ⊆ U) :
    ∃ G : I × Icc (-1 : ℝ) 1 → S,
      IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
      (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend ((M : ℝ)*t)) ∧
      Set.range G ∩ Set.range p = p '' Icc 0 M ∧
      Set.range G ⊆ Set.range E ∪ U := by
  have advance {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m n : I) (hm0 : 0 < m) (hmn : m < n)
      (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
      (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
      (e : OpenPartialHomeomorph S Plane) (hps : p '' Icc m n ⊆ e.source)
      (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m n ⊆ U)
      (k : ℝ) (hk : 0 < k ∧ k < 1) :
      let M : I := ⟨(m : ℝ)+((n : ℝ)-m)*k,by
        constructor
        · nlinarith [m.property.1,show (m : ℝ)<n from hmn]
        · have hb := mul_le_mul_of_nonneg_left hk.2.le (sub_pos.mpr (show (m : ℝ)<n from hmn)).le
          nlinarith [n.property.2]⟩
      ∃ G : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
        (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend ((M : ℝ)*t)) ∧
        Set.range G ∩ Set.range p = p '' Icc 0 M ∧
        Set.range G ⊆ Set.range E ∪ U := by
    apply outsideBandsPackaging_360_advance <;> assumption
  have atlas {x y : S} (p : Path x y) (m M : I) (hmM : m ≤ M) (hM1 : M < 1)
      (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m M ⊆ U) :
      ∃ τ : ℕ → I, τ 0 = m ∧ Monotone τ ∧
        (∃ N, ∀ j ≥ N, τ j = M) ∧
        ∀ j, ∃ (e : OpenPartialHomeomorph S Plane) (n : I),
          τ (j+1) < n ∧ p '' Icc (τ j) n ⊆ e.source ∩ U := by
    apply outsideBandsPackaging_1431_atlas <;> assumption
  obtain ⟨τ,hτ0,hτmono,⟨N,hτend⟩,hτchart⟩ := atlas p m M hmM hM1 U hU hpU
  have hτpos (j : ℕ) : 0 < τ j := by
    have hh := hτmono (Nat.zero_le j)
    rw [hτ0] at hh
    exact hm0.trans_le hh
  have hsteps (j : ℕ) :
      ∃ G : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
        (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend ((τ j : ℝ)*t)) ∧
        Set.range G ∩ Set.range p = p '' Icc 0 (τ j) ∧
        Set.range G ⊆ Set.range E ∪ U := by
    as_aux_lemma =>
      induction j with
      | zero =>
        rw [hτ0]
        exact ⟨E,hE,fun _ => rfl,hcenter,hmeet,Set.subset_union_left⟩
      | succ j ih =>
        by_cases heq : τ j = τ (j+1)
        · simpa only [← heq] using ih
        · have hlt : τ j < τ (j+1) := lt_of_le_of_ne (hτmono (Nat.le_succ j)) heq
          obtain ⟨G,hG,hG0,hGc,hGmeet,hGU⟩ := ih
          obtain ⟨e,n,hn,hps⟩ := hτchart j
          have hjn : τ j < n := hlt.trans hn
          let k : ℝ := ((τ (j+1):ℝ)-τ j)/((n:ℝ)-τ j)
          have hd : 0 < (n:ℝ)-τ j := sub_pos.mpr hjn
          have hk : 0 < k ∧ k < 1 := by
            dsimp [k]
            constructor
            · exact div_pos (sub_pos.mpr hlt) hd
            · apply (div_lt_one hd).mpr
              exact sub_lt_sub_right (show (τ (j+1):ℝ)<n from hn) _
          have hcalc : (τ j:ℝ)+((n:ℝ)-τ j)*k = τ (j+1) := by
            dsimp [k]
            field_simp
            <;> ring
          let dest : I := ⟨(τ j:ℝ)+((n:ℝ)-τ j)*k,by
            constructor
            · nlinarith [(τ j).property.1,hjn]
            · have hb := mul_le_mul_of_nonneg_left hk.2.le (sub_pos.mpr (show (τ j:ℝ)<n from hjn)).le
              nlinarith [n.property.2]⟩
          have hdest : dest = τ (j+1) := Subtype.ext hcalc
          have hadv := advance p hp (τ j) n (hτpos j) hjn G hG hGc hGmeet e
            (fun z hz => (hps hz).1) U hU (fun z hz => (hps hz).2) k hk
          change ∃ H : I × Icc (-1 : ℝ) 1 → S,
            IsEmbedding H ∧ (∀ w,H (0,w)=G (0,w)) ∧
            (∀ t : I,H (t,⟨0,by norm_num⟩)=p.extend ((dest:ℝ)*t)) ∧
            Set.range H ∩ Set.range p=p '' Icc 0 dest ∧
            Set.range H ⊆ Set.range G ∪ U at hadv
          rw [hdest] at hadv
          obtain ⟨H,hH,hH0,hHc,hHmeet,hHU⟩ := hadv
          refine ⟨H,hH,fun w => (hH0 w).trans (hG0 w),hHc,hHmeet,?_⟩
          intro z hz
          rcases hHU hz with hg | hu
          · exact hGU hg
          · exact Or.inr hu
  have hfinal := hsteps N
  rw [hτend N le_rfl] at hfinal
  exact hfinal

private theorem outsideBandsPackaging_216_actualPrefix {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b)
    (M : I) (hM0 : 0 < M) (hM1 : M < 1)
    (K : Set S) (hK : IsClosed K)
    (hKa : Disjoint (Set.range D.firstArc) K)
    (hKe : Disjoint (Set.range (D.ends 2)) K) :
    ∃ G : I × BandWidth → S, IsEmbedding G ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧ Disjoint (Set.range G) K := by
  have initial {a b : Curve S} (D : OneCrossingBandBase a b)
      (m : I) (hm0 : 0 < m) (hm1 : m < 1)
      (hmends : D.firstArc '' Icc 0 m ⊆ Set.range (D.ends 2)) :
      ∃ E : I × BandWidth → S, IsEmbedding E ∧
        (∀ w, E (0,w) = D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I, E (t,⟨0,by norm_num⟩) = D.firstArc.extend ((m : ℝ)*t)) ∧
        Set.range E ∩ Set.range D.firstArc = D.firstArc '' Icc 0 m ∧
        Set.range E ∩ Set.range D.square = Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range E) (Set.range D.secondArc) ∧ Set.range E ⊆ Set.range (D.ends 2) := by
    apply outsideBandsPackaging_228_initial <;> assumption
  have iterate {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (m M : I) (hm0 : 0 < m) (hmM : m ≤ M) (hM1 : M < 1)
      (E : I × Icc (-1 : ℝ) 1 → S) (hE : IsEmbedding E)
      (hcenter : ∀ t : I, E (t,⟨0,by norm_num⟩) = p.extend ((m : ℝ)*t))
      (hmeet : Set.range E ∩ Set.range p = p '' Icc 0 m)
      (U : Set S) (hU : IsOpen U) (hpU : p '' Icc m M ⊆ U) :
      ∃ G : I × Icc (-1 : ℝ) 1 → S,
        IsEmbedding G ∧ (∀ w, G (0,w) = E (0,w)) ∧
        (∀ t : I, G (t,⟨0,by norm_num⟩) = p.extend ((M : ℝ)*t)) ∧
        Set.range G ∩ Set.range p = p '' Icc 0 M ∧
        Set.range G ⊆ Set.range E ∪ U := by
    apply outsideBandsPackaging_349_iterate <;> assumption
  obtain ⟨η,ηfar,hη,hηfar,hstart,hfar⟩ := D.first_endpoint_rectangles_cover_tails
  let d : ℝ := min (η/2) ((M:ℝ)/2)
  have hd : 0 < d := lt_min (by linarith) (by have hh : (0:ℝ)<M := hM0; linarith)
  have hdM : d < (M:ℝ) := by
    have hh := min_le_right (η/2) ((M:ℝ)/2)
    have hpos : (0:ℝ)<M := hM0
    dsimp [d]; linarith
  have hdη : d < η := by have hh := min_le_left (η/2) ((M:ℝ)/2); dsimp [d]; linarith
  let m : I := ⟨d,⟨hd.le,hdM.le.trans M.property.2⟩⟩
  have hm0 : 0 < m := hd
  have hmM : m < M := hdM
  have hm1 : m < 1 := hmM.trans hM1
  have hmends : D.firstArc '' Icc 0 m ⊆ Set.range (D.ends 2) := by
    rintro z ⟨t,ht,rfl⟩
    exact hstart t (lt_of_le_of_lt ht.2 hdη)
  obtain ⟨E,hE,hE0,hEc,hEmeet,hEQ,hEsecond,hEsub⟩ := initial D m hm0 hm1 hmends
  let U : Set S := ((Set.range D.square ∪ Set.range D.secondArc) ∪ K)ᶜ
  have hU : IsOpen U := (((isCompact_range D.square_embedded.continuous).isClosed.union
    (isCompact_range D.secondArc.continuous).isClosed).union hK).isOpen_compl
  have hpU : D.firstArc '' Icc m M ⊆ U := by
    as_aux_lemma =>
      rintro z ⟨t,ht,rfl⟩ hz
      rcases hz with (hq | hb) | hk
      · have hh : D.firstArc t ∈ ({D.firstArc 0,D.firstArc 1}:Set S) :=
          D.firstArc_square_intersection ▸ ⟨Set.mem_range_self _,hq⟩
        rcases Set.mem_insert_iff.mp hh with he | he
        · have ht0 := D.firstArc_embedded.injective he
          have hpos : 0 < t := hm0.trans_le ht.1
          rw [ht0] at hpos
          exact lt_irrefl _ hpos
        · have he1 : D.firstArc t=D.firstArc 1 := he
          have ht1 := D.firstArc_embedded.injective he1
          have hlt : t < 1 := ht.2.trans_lt hM1
          rw [ht1] at hlt
          exact lt_irrefl _ hlt
      · exact Set.disjoint_left.mp D.arcs_disjoint (Set.mem_range_self _) hb
      · exact Set.disjoint_left.mp hKa (Set.mem_range_self _) hk
  obtain ⟨G,hG,hG0,hGc,hGmeet,hGU⟩ := iterate D.firstArc D.firstArc_embedded m M hm0 hmM.le hM1 E hE hEc hEmeet U hU hpU
  refine ⟨G,hG,fun w => (hG0 w).trans (hE0 w),hGc,hGmeet,?_,?_,?_⟩
  · apply Set.Subset.antisymm
    · rintro z ⟨hz,hq⟩
      rcases hGU hz with he | hu
      · exact hEQ ▸ ⟨he,hq⟩
      · exact False.elim (hu (Or.inl (Or.inl hq)))
    · rintro z ⟨w,rfl⟩
      refine ⟨⟨(0,w),?_⟩,Set.mem_range_self _⟩
      exact (hG0 w).trans (hE0 w)
  · apply Set.disjoint_left.mpr
    intro z hz hb
    rcases hGU hz with he | hu
    · exact Set.disjoint_left.mp hEsecond he hb
    · exact hu (Or.inl (Or.inr hb))
  · apply Set.disjoint_left.mpr
    intro z hz hk
    rcases hGU hz with he | hu
    · exact Set.disjoint_left.mp hKe (hEsub he) hk
    · exact hu (Or.inr hk)

private theorem outsideBandsPackaging_196_source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ M : I, 0 < M ∧ M < 1 ∧
    ∃ G : I × BandWidth → S, IsEmbedding G ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧
      Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
    ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ C : EndRectangle → S, IsEmbedding C ∧
      Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
        (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
      (∀ z, C z = G
        (⟨1-2*r+r*(z.1:ℝ),by
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
      ∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0 := by
  have actualPrefix {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (M : I) (hM0 : 0 < M) (hM1 : M < 1)
      (K : Set S) (hK : IsClosed K)
      (hKa : Disjoint (Set.range D.firstArc) K)
      (hKe : Disjoint (Set.range (D.ends 2)) K) :
      ∃ G : I × BandWidth → S, IsEmbedding G ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧ Disjoint (Set.range G) K := by
    apply outsideBandsPackaging_216_actualPrefix <;> assumption
  have restrict (E : I × BandWidth → S) (hE : IsEmbedding E)
      (U : Set S) (hU : IsOpen U) (hend : E (1,⟨0,by norm_num⟩) ∈ U) :
      ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : EndRectangle → S, IsEmbedding C ∧ Set.range C ⊆ U ∧
        ∀ z, C z = E
          (⟨1-2*r+r*(z.1:ℝ),by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
           ⟨δ*(z.2:ℝ),by
              constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩) := by
    as_aux_lemma =>
      obtain ⟨d,hd,hdU⟩ := Metric.mem_nhds_iff.mp
        (hE.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hend))
      let r := min (d/8) (1/8:ℝ)
      let δ := min (d/4) (1/2:ℝ)
      have hr0 : 0 < r := lt_min (by positivity) (by norm_num)
      have hr1 : r < 1/4 := (min_le_right _ _).trans_lt (by norm_num)
      have hδ0 : 0 < δ := lt_min (by positivity) (by norm_num)
      have hδ1 : δ ≤ 1 := (min_le_right _ _).trans (by norm_num)
      have hrd : 3*r < d := by have := min_le_left (d/8) (1/8:ℝ); dsimp [r]; linarith
      have hδd : δ < d := by have := min_le_left (d/4) (1/2:ℝ); dsimp [δ]; linarith
      let k : EndRectangle → I × BandWidth := fun z =>
        (⟨1-2*r+r*(z.1:ℝ),by
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr0,hr1]⟩,
         ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ0,hδ1]⟩)
      have hkc : Continuous k := by dsimp [k]; fun_prop
      have hki : Function.Injective k := by
        as_aux_lemma =>
          intro z w he
          apply Prod.ext <;> apply Subtype.ext
          · have hh := congrArg (fun q : I × BandWidth => (q.1:ℝ)) he
            change 1-2*r+r*(z.1:ℝ)=1-2*r+r*(w.1:ℝ) at hh
            nlinarith
          · have hh := congrArg (fun q : I × BandWidth => (q.2:ℝ)) he
            exact mul_left_cancel₀ hδ0.ne' hh
      refine ⟨r,δ,⟨hr0,hr1⟩,⟨hδ0,hδ1⟩,E ∘ k,
        hE.comp (hkc.isClosedEmbedding hki).isEmbedding,?_,fun _ => rfl⟩
      rintro x ⟨z,rfl⟩
      apply hdU
      change dist (k z) ((1:I),⟨0,by norm_num⟩) < d
      rw [Prod.dist_eq,Subtype.dist_eq,Subtype.dist_eq,Real.dist_eq,Real.dist_eq]
      change max |1-2*r+r*(z.1:ℝ)-1| |δ*(z.2:ℝ)-0| < d
      apply max_lt
      · rw [abs_of_nonpos (by nlinarith [z.1.property.2,hr0])]
        nlinarith [z.1.property.1,hrd]
      · rw [sub_zero,abs_mul,abs_of_pos hδ0]
        exact ((mul_le_mul_of_nonneg_left (abs_le.mpr z.2.property) hδ0.le).trans (by simp)).trans_lt hδd
  have hend : D.firstArc (1:I) ∈ interior (Set.range (D.ends 0)) := by
    rw [D.firstArc.target,←D.ends_seam]
    exact endRectangle_center_interior (D.ends 0) (D.ends_embedded 0)
  obtain ⟨η,hη,hηtail⟩ := Metric.mem_nhds_iff.mp
    (D.firstArc.continuous.continuousAt.preimage_mem_nhds
      (isOpen_interior.mem_nhds hend))
  let d := min (η/2) (1/2:ℝ)
  have hd0 : 0 < d := lt_min (half_pos hη) (by norm_num)
  have hd1 : d < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hdη : d < η := (min_le_left _ _).trans_lt (half_lt_self hη)
  let M : I := ⟨1-d,⟨by linarith,by linarith⟩⟩
  have hM0 : 0 < M := by change 0 < 1-d; linarith
  have hM1 : M < 1 := by change 1-d < 1; linarith
  have hMend : D.firstArc M ∈ interior (Set.range (D.ends 0)) := by
    apply hηtail
    change dist M (1:I) < η
    rw [Subtype.dist_eq,Real.dist_eq]
    change |1-d-1| < η
    simpa [abs_of_nonneg hd0.le] using hdη
  let K := Set.range (D.ends 1) ∪ Set.range (D.ends 3)
  have hK : IsClosed K := (isCompact_range (D.ends_embedded 1).continuous).isClosed.union
    (isCompact_range (D.ends_embedded 3).continuous).isClosed
  have hKa : Disjoint (Set.range D.firstArc) K := by
    as_aux_lemma =>
      apply Set.disjoint_left.mpr
      intro x hx hKx
      have hxa : x ∈ a.image := (D.firstArc_range ▸ hx).1
      rcases hKx with ⟨z,hz⟩ | ⟨z,hz⟩
      · have hh := ((D.ends_axes 1 z).1.mp (hz.symm ▸ hxa)).1
        norm_num at hh
      · have hh := ((D.ends_axes 3 z).1.mp (hz.symm ▸ hxa)).1
        norm_num at hh
  have hKe : Disjoint (Set.range (D.ends 2)) K := by
    apply Set.disjoint_left.mpr
    intro x hx hKx
    rcases hKx with h1 | h3
    · exact Set.disjoint_left.mp (D.ends_disjoint (show (2:Fin 4)≠1 by decide)) hx h1
    · exact Set.disjoint_left.mp (D.ends_disjoint (show (2:Fin 4)≠3 by decide)) hx h3
  obtain ⟨G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK⟩ := actualPrefix D M hM0 hM1 K hK hKa hKe
  have hGa (z : I × BandWidth) : G z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0 := by
    as_aux_lemma =>
      constructor
      · intro hz
        have hm : G z ∈ D.firstArc '' Icc 0 M := hGmeet ▸ ⟨Set.mem_range_self z,hz⟩
        obtain ⟨t,ht,he⟩ := hm
        let u : I := ⟨(t:ℝ)/(M:ℝ),⟨div_nonneg t.property.1 hM0.le,
          (div_le_one (show 0<(M:ℝ) from hM0)).mpr ht.2⟩⟩
        have hu : (M:ℝ)*(u:ℝ)=(t:ℝ) := by dsimp [u]; field_simp [ne_of_gt hM0]
        have hGsame : G (u,⟨0,by norm_num⟩) = G z := by
          rw [hGc,hu,Path.extend_extends']
          exact he
        have hh := congrArg (fun q : I × BandWidth => (q.2:ℝ)) (hG.injective hGsame)
        exact hh.symm
      · intro hz
        have hw : z.2 = ⟨0,by norm_num⟩ := Subtype.ext hz
        let t : I := ⟨(M:ℝ)*(z.1:ℝ),by
          constructor <;> nlinarith [M.property.1,M.property.2,z.1.property.1,z.1.property.2]⟩
        refine ⟨t,?_⟩
        calc D.firstArc t = D.firstArc.extend ((M:ℝ)*(z.1:ℝ)) :=
            (D.firstArc.extend_extends' t).symm
          _ = G (z.1,⟨0,by norm_num⟩) := (hGc z.1).symm
          _ = G z := by rw [←hw]
  let U := interior (Set.range (D.ends 0)) ∩
    (Set.range D.square ∪ Set.range D.secondArc)ᶜ
  have hU : IsOpen U := isOpen_interior.inter
    (((isCompact_range D.square_embedded.continuous).isClosed.union
      (isCompact_range D.secondArc.continuous).isClosed).isOpen_compl)
  have hGM : G (1,⟨0,by norm_num⟩) = D.firstArc M := by
    rw [hGc]
    simpa using D.firstArc.extend_extends' M
  have hGU : G (1,⟨0,by norm_num⟩) ∈ U := by
    as_aux_lemma =>
      rw [hGM]
      refine ⟨hMend,?_⟩
      rintro (hQ | hother)
      · have hh := D.firstArc_square_intersection ▸
          (show D.firstArc M ∈ Set.range D.firstArc ∩ Set.range D.square from
            ⟨Set.mem_range_self _,hQ⟩)
        rcases Set.mem_insert_iff.mp hh with he | he
        · have h0 := D.firstArc_embedded.injective he
          exact (ne_of_gt hM0) h0
        · have h1 := D.firstArc_embedded.injective (show D.firstArc M=D.firstArc 1 from he)
          exact (ne_of_lt hM1) h1
      · exact Set.disjoint_left.mp D.arcs_disjoint (Set.mem_range_self _) hother
  obtain ⟨r,δ,hr,hδ,C,hC,hCU,hformula⟩ := restrict G hG U hU hGU
  refine ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,?_⟩
  intro z
  rw [hformula,hGa]
  change δ*(z.2:ℝ)=0 ↔ (z.2:ℝ)=0
  simp [hδ.1.ne']

private theorem outsideBandsPackaging_169_source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ M : I, 0 < M ∧ M < 1 ∧
    ∃ G : I × BandWidth → S, IsEmbedding G ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧
      Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
    ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ C : EndRectangle → S, IsEmbedding C ∧
      Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
        (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
      (∀ z, C z = G
        (⟨1-2*r+r*(z.1:ℝ),by
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
      (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
      ∃ c : EndRectangle → Plane, IsEmbedding c ∧
        (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
        ∃ height : BandWidth → ℝ, Continuous height ∧
          (∀ t, 0 < height t ∧ height t ≤ 1) ∧
          (StrictMono height ∨ StrictAnti height) ∧
          ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0 := by
  have source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ M : I, 0 < M ∧ M < 1 ∧
      ∃ G : I × BandWidth → S, IsEmbedding G ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧
        Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : EndRectangle → S, IsEmbedding C ∧
        Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
          (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
        (∀ z, C z = G
          (⟨1-2*r+r*(z.1:ℝ),by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
           ⟨δ*(z.2:ℝ),by
              constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
        ∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0 := by
    apply outsideBandsPackaging_196_source <;> assumption
  have coordinates {S : Type} [TopologicalSpace S] [T2Space S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (C : EndRectangle → S) (hC : IsEmbedding C)
      (hends : Set.range C ⊆ Set.range (D.ends 0))
      (houtside : Disjoint (Set.range C) (Set.range D.square))
      (haxisC : ∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) :
      ∃ c : EndRectangle → Plane, IsEmbedding c ∧
        (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
        ∃ height : BandWidth → ℝ, Continuous height ∧
          (∀ t, 0 < height t ∧ height t ≤ 1) ∧
          (StrictMono height ∨ StrictAnti height) ∧
          ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0 := by
    apply outsideBandsPackaging_1735_coordinates <;> assumption
  obtain ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC⟩ := source D
  have hends : Set.range C ⊆ Set.range (D.ends 0) := fun x hx => interior_subset (hCU hx).1
  have houtside : Disjoint (Set.range C) (Set.range D.square) := by
    apply Set.disjoint_left.mpr
    intro x hx hQ
    exact (hCU hx).2 (Or.inl hQ)
  obtain ⟨c,hc,hcaxis,hcformula,height,hheight,hhb,hmono,hc0⟩ := coordinates D C hC hends houtside haxisC
  refine ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC,
    c,hc,hcaxis,hcformula,height,hheight,hhb,hmono,hc0⟩

private theorem outsideBandsPackaging_132_source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ M : I, 0 < M ∧ M < 1 ∧
    ∃ G : I × BandWidth → S, IsEmbedding G ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧
      Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
    ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ C : EndRectangle → S, IsEmbedding C ∧
      Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
        (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
      (∀ z, C z = G
        (⟨1-2*r+r*(z.1:ℝ),by
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
      (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
      ∃ c : EndRectangle → Plane, IsEmbedding c ∧
        (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
        ∃ height : BandWidth → ℝ, Continuous height ∧
          (∀ t, 0 < height t ∧ height t ≤ 1) ∧
          StrictAnti height ∧
          (∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0) ∧
    ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
      ∀ x : ℝ, |x| ≤ 2 →
        0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
        (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1 := by
  have source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ M : I, 0 < M ∧ M < 1 ∧
      ∃ G : I × BandWidth → S, IsEmbedding G ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧
        Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : EndRectangle → S, IsEmbedding C ∧
        Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
          (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
        (∀ z, C z = G
          (⟨1-2*r+r*(z.1:ℝ),by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
           ⟨δ*(z.2:ℝ),by
              constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
        (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
        ∃ c : EndRectangle → Plane, IsEmbedding c ∧
          (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
          (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
          ∃ height : BandWidth → ℝ, Continuous height ∧
            (∀ t, 0 < height t ∧ height t ≤ 1) ∧
            (StrictMono height ∨ StrictAnti height) ∧
            ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0 := by
    apply outsideBandsPackaging_169_source <;> assumption
  have window (height : BandWidth → ℝ) (hh : Continuous height)
      (hm : StrictMono height ∨ StrictAnti height)
      (hb : ∀ t, 0 < height t ∧ height t ≤ 1) :
      ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
        ∀ x : ℝ, |x| ≤ 2 →
          0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
          (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1 := by
    apply outsideBandsPackaging_1821_window <;> assumption
  have axisParameter {S : Type} [TopologicalSpace S] [T2Space S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ γ : I → I, Continuous γ ∧ StrictAnti γ ∧ γ 0=1 ∧ 0<γ 1 ∧
        (∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
          constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y)) ∧
        ∀ y : I,D.firstArc '' Icc (γ y) 1 ⊆ Set.range (D.ends 0) := by
    apply outsideBandsPackaging_1882_axisParameter <;> assumption
  have direction {S : Type} [TopologicalSpace S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (γ : I → I) (hγ : StrictAnti γ)
      (hγaxis : ∀ y : I,D.ends 0 (⟨0,by norm_num⟩,⟨(y:ℝ),by
        constructor <;> linarith [y.property.1,y.property.2]⟩)=D.firstArc (γ y))
      (M : I) (hM : 0 < M) (r : ℝ) (hr : 0 < r ∧ r < 1/4)
      (height : BandWidth → ℝ) (hb : ∀ t,0 < height t ∧ height t ≤ 1)
      (hcenter : ∀ t : BandWidth,D.ends 0
        (⟨0,by norm_num⟩,⟨height t,by constructor <;> linarith [(hb t).1,(hb t).2]⟩)=
          D.firstArc.extend ((M:ℝ)*(1-2*r+r*(t:ℝ)))) :
      StrictAnti height := by
    apply outsideBandsPackaging_1949_direction (S := S) <;> assumption
  obtain ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC,
    c,hc,hcaxis,hcformula,height,hheight,hhb,hmono,hc0⟩ := source D
  obtain ⟨γ,hγc,hγanti,hγ0,hγ1,hγaxis,hγtail⟩ := axisParameter D
  have hcenterheight (t : BandWidth) : D.ends 0
      (⟨0,by norm_num⟩,⟨height t,by constructor <;> linarith [(hhb t).1,(hhb t).2]⟩)=
        D.firstArc.extend ((M:ℝ)*(1-2*r+r*(t:ℝ))) := by
    as_aux_lemma =>
      obtain ⟨v,hv,hcv⟩ := hcformula (t,⟨0,by norm_num⟩)
      have hcaxis0 := hc0 t
      have hh : Plane.mk (v.2:ℝ) (v.1:ℝ)=Plane.mk (height t) 0 := hcv.symm.trans hcaxis0
      have hv0 : (v.1:ℝ)=0 := congrArg (fun p : Plane => p 1) hh
      have hv1 : (v.2:ℝ)=height t := congrArg (fun p : Plane => p 0) hh
      have he : v=(⟨0,by norm_num⟩,⟨height t,by constructor <;> linarith [(hhb t).1,(hhb t).2]⟩) := by
        apply Prod.ext <;> apply Subtype.ext
        · exact hv0
        · exact hv1
      rw [←he,hv,hformula]
      simp only [Prod.fst,Prod.snd,mul_zero]
      rw [hGc]
  have hanti := direction D γ hγanti hγaxis M hM0 r hr height hhb hcenterheight
  obtain ⟨s,hs,hwindow⟩ := window height hheight hmono hhb
  refine ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC,
    c,hc,hcaxis,hcformula,height,hheight,hhb,hanti,hc0,s,hs,hwindow⟩

private theorem outsideBandsPackaging_55_source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ M : I, 0 < M ∧ M < 1 ∧
    ∃ G : I × BandWidth → S, IsEmbedding G ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧
      Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
    ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
    ∃ C : EndRectangle → S, IsEmbedding C ∧
      Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
        (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
      (∀ z, C z = G
        (⟨1-2*r+r*(z.1:ℝ),by
            constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by
            constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
      (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
      ∃ c : EndRectangle → Plane, IsEmbedding c ∧
        (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
        ∃ height : BandWidth → ℝ, Continuous height ∧
          (∀ t, 0 < height t ∧ height t ≤ 1) ∧
          StrictAnti height ∧
          (∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0) ∧
    ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
      (∀ x : ℝ, |x| ≤ 2 →
        0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
        (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
             height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
             height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1) ∧
    ∃ q : I → BandWidth, Continuous q ∧ Function.Injective q ∧
      (∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ))) ∧
    ∃ P : I × BandWidth → Plane, IsEmbedding P ∧
      (∀ z,P z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)) ∧
    ∃ h : I → ℝ, Continuous h ∧ StrictMono h ∧
      (∀ t,h t=height (q t)) ∧
      (∀ t : I,P (t,⟨0,by norm_num⟩)=Plane.mk (h t) 0) ∧
      (∀ z,P z 1=0 ↔ (z.2:ℝ)=0) ∧
      (∀ x : ℝ, |x| ≤ 2 →
        0 < (h 0+h 1)/2+(h 1-h 0)/2*x ∧
        (h 0+h 1)/2+(h 1-h 0)/2*x < 1) ∧
    ∃ A : I ≃ₜ I,
      (∀ t : I,h (A t)=h 0+(h 1-h 0)*(t:ℝ)) ∧
    ∃ width : ℝ, 0 < width ∧ width ≤ 1 ∧
    ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
      (∀ z, z ∉ Plane.openSquare 0 2 → H z=z) ∧
      (∀ x : ℝ,H (Plane.mk x 0)=Plane.mk x 0) ∧
      (∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
          Plane.mk ((2*(P (A t,w) 0-h 0))/(h 1-h 0)-1)
            (P (A t,w) 1)) ∧
    ∃ E : ↥(Plane.closedSquare 0 1) → S, IsEmbedding E ∧
      Set.range E ⊆ Set.range (D.ends 0) ∧
      Disjoint (Set.range E) (Set.range D.square) ∧
      (∀ z, ∃ v : EndRectangle, D.ends 0 v=E z ∧
        (v.1:ℝ)=(z.val 1)/2 ∧ (v.2:ℝ)=((h 0+h 1)/2)+((h 1-h 0)/2)*(2*z.val 0)) ∧
      ∃ F : S ≃ₜ S,
        (∀ x, x ∉ Set.range (D.ends 0) → F x=x) ∧
        (∀ x, x ∈ a.image → F x=x) ∧
        (∀ x, x ∈ b.image → F x=x) ∧
        (∀ x, x ∈ Set.range D.square → F x=x) ∧
(        ∀ z : ↥(Plane.closedSquare 0 1),
          ∃ w : ↥(Plane.closedSquare 0 1),
            w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w) ∧
    ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth, ∃ v : EndRectangle,
      (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
      (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
      (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*z.val 0 ∧
      F (D.ends 0 v)=C (q (A t),w) := by
  have source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ M : I, 0 < M ∧ M < 1 ∧
      ∃ G : I × BandWidth → S, IsEmbedding G ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧
        Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : EndRectangle → S, IsEmbedding C ∧
        Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
          (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
        (∀ z, C z = G
          (⟨1-2*r+r*(z.1:ℝ),by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
           ⟨δ*(z.2:ℝ),by
              constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
        (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
        ∃ c : EndRectangle → Plane, IsEmbedding c ∧
          (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
          (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
          ∃ height : BandWidth → ℝ, Continuous height ∧
            (∀ t, 0 < height t ∧ height t ≤ 1) ∧
            StrictAnti height ∧
            (∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0) ∧
      ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
        ∀ x : ℝ, |x| ≤ 2 →
          0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
          (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1 := by
    apply outsideBandsPackaging_132_source <;> assumption
  have prepare (c : EndRectangle → Plane) (hc : IsEmbedding c)
      (height : BandWidth → ℝ) (hh : Continuous height)
      (ha : StrictAnti height)
      (hc0 : ∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
      (haxis : ∀ z,c z 1=0 ↔ (z.2:ℝ)=0)
      (s : ℝ) (hs : 0 < s ∧ s ≤ 1/2)
      (hwindow : ∀ x : ℝ, |x| ≤ 2 →
        0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩+
          height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩-
            height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
        (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩+
          height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
          (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩-
            height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1) :
      ∃ q : I → BandWidth, Continuous q ∧ Function.Injective q ∧
        (∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ))) ∧
      ∃ C : I × BandWidth → Plane, IsEmbedding C ∧
        (∀ z,C z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)) ∧
      ∃ h : I → ℝ, Continuous h ∧ StrictMono h ∧
        (∀ t,h t=height (q t)) ∧
        (∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (h t) 0) ∧
        (∀ z,C z 1=0 ↔ (z.2:ℝ)=0) ∧
        ∀ x : ℝ, |x| ≤ 2 →
          0 < (h 0+h 1)/2+(h 1-h 0)/2*x ∧
          (h 0+h 1)/2+(h 1-h 0)/2*x < 1 := by
    apply outsideBandsPackaging_2008_prepare <;> assumption
  have straighten (C : I × BandWidth → Plane) (hC : IsEmbedding C)
      (height : I → ℝ) (hh : Continuous height) (hm : StrictMono height)
      (hc : ∀ t : I,C (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0)
      (haxis : ∀ z, C z 1=0 ↔ (z.2:ℝ)=0) :
      ∃ A : I ≃ₜ I,
        (∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) ∧
      ∃ width : ℝ, 0 < width ∧ width ≤ 1 ∧
      ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 2 → H z=z) ∧
        (∀ x : ℝ,H (Plane.mk x 0)=Plane.mk x 0) ∧
        ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
          (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
          H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
            Plane.mk ((2*(C (A t,w) 0-height 0))/(height 1-height 0)-1)
              (C (A t,w) 1) := by
    apply outsideBandsPackaging_2090_straighten <;> assumption
  have surface {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (center span : ℝ) (hspan : span ≠ 0)
      (hwindow : ∀ x : ℝ, |x| ≤ 2 → 0 < center+span*x ∧ center+span*x < 1)
      (H : Plane ≃ₜ Plane)
      (hfix : ∀ z, z ∉ Plane.openSquare 0 2 → H z=z)
      (haxis : ∀ t : ℝ,H (Plane.mk t 0)=Plane.mk t 0) :
      ∃ E : ↥(Plane.closedSquare 0 1) → S, IsEmbedding E ∧
        Set.range E ⊆ Set.range (D.ends 0) ∧
        Disjoint (Set.range E) (Set.range D.square) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v=E z ∧
          (v.1:ℝ)=(z.val 1)/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0)) ∧
        ∃ F : S ≃ₜ S,
          (∀ x, x ∉ Set.range (D.ends 0) → F x=x) ∧
          (∀ x, x ∈ a.image → F x=x) ∧
          (∀ x, x ∈ b.image → F x=x) ∧
          (∀ x, x ∈ Set.range D.square → F x=x) ∧
          ∀ z : ↥(Plane.closedSquare 0 1),
            ∃ w : ↥(Plane.closedSquare 0 1),
              w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w := by
    apply outsideBandsPackaging_3262_surface <;> assumption
  have native {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b)
      (C : EndRectangle → S) (c : EndRectangle → Plane)
      (hc : ∀ z, ∃ v : EndRectangle,D.ends 0 v=C z ∧ c z=Plane.mk v.2 v.1)
      (q : I → BandWidth) (P : I × BandWidth → Plane)
      (hP : ∀ z,P z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1))
      (h : I → ℝ) (hd : h 1-h 0 ≠ 0)
      (width : ℝ) (A : I ≃ₜ I) (flip : Bool) (H : Plane ≃ₜ Plane)
      (hH : ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
          Plane.mk ((2*(P (A t,w) 0-h 0))/(h 1-h 0)-1) (P (A t,w) 1))
      (E : ↥(Plane.closedSquare 0 1) → S)
      (hE : ∀ z, ∃ v : EndRectangle,D.ends 0 v=E z ∧
        (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*(2*z.val 0))
      (F : S ≃ₜ S)
      (hF : ∀ z : ↥(Plane.closedSquare 0 1), ∃ w : ↥(Plane.closedSquare 0 1),
        w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w) :
      ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth, ∃ v : EndRectangle,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
        (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*z.val 0 ∧
        F (D.ends 0 v)=C (q (A t),w) := by
    apply outsideBandsPackaging_3488_native <;> assumption
  obtain ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC,
    c,hc,hcaxis,hcformula,height,hheight,hhb,hmono,hc0,s,hs,hwindow⟩ := source D
  obtain ⟨q,hqc,hqi,hqform,P,hP,hPformula,h,hh,hm,hform,hPc,hPaxis,hphyswindow⟩ :=
    prepare c hc height hheight hmono hc0 hcaxis s hs hwindow
  obtain ⟨A,hA,width,hw0,hw1,flip,H,hHfix,hHaxis,hHformula⟩ :=
    straighten P hP h hh hm hPc hPaxis
  have hspan : (h 1-h 0)/2 ≠ 0 := by
    have hd := sub_pos.mpr (hm (show (0:I)<1 by norm_num))
    positivity
  obtain ⟨E,hE,hEs,hEq,hEformula,F,hFoutside,hFa,hFb,hFQ,hFE⟩ :=
    surface D ((h 0+h 1)/2) ((h 1-h 0)/2) hspan hphyswindow H hHfix hHaxis
  refine ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hformula,haxisC,
    c,hc,hcaxis,hcformula,height,hheight,hhb,hmono,hc0,s,hs,hwindow,
    q,hqc,hqi,hqform,P,hP,hPformula,h,hh,hm,hform,hPc,hPaxis,hphyswindow,
    A,hA,width,hw0,hw1,flip,H,hHfix,hHaxis,hHformula,
    E,hE,hEs,hEq,hEformula,F,hFoutside,hFa,hFb,hFQ,hFE,?_⟩

  exact native D C c hcformula q P hPformula h (by
    exact ne_of_gt (sub_pos.mpr (hm (show (0:I)<1 by norm_num))))
    width A flip H hHformula E hEformula F hFE

private theorem outsideBandsPackaging_32_align {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ M τ c cut : I, 0<M ∧ M<1 ∧ 0<τ ∧ τ<1 ∧ 0<c ∧ c<1 ∧
      0<cut ∧ cut<1 ∧ (cut:ℝ)=(M:ℝ)*τ ∧
    ∃ η : ℝ,∃ hη : 0<η ∧ η≤1,
    ∃ flip : Bool,∃ G R : I × BandWidth → S,
      IsEmbedding G ∧ IsEmbedding R ∧
      (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
      Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
      Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      Disjoint (Set.range G) (Set.range D.secondArc) ∧
      Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      (∀ w,R (0,w)=G (τ,⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)) ∧
      (∀ w,R (1,w)=D.square (squarePort D.radius D.radius_pos 0 (flipBandWidth flip w))) ∧
      (∀ t : I,R (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t)) ∧
      (∀ z,R z∈Set.range D.firstArc ↔ (z.2:ℝ)=0) ∧
      Disjoint (Set.range R) (Set.range D.secondArc) ∧
      Set.range R ⊆ Set.range (D.ends 0) ∧
      Set.range R ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
      ∀ t : I,c≤t → ∀ w : BandWidth,
        G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
           ⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)∈Set.range R ↔ t=1 := by
  have source {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ M : I, 0 < M ∧ M < 1 ∧
      ∃ G : I × BandWidth → S, IsEmbedding G ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧
        Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      ∃ r δ : ℝ, ∃ hr : 0 < r ∧ r < 1/4, ∃ hδ : 0 < δ ∧ δ ≤ 1,
      ∃ C : EndRectangle → S, IsEmbedding C ∧
        Set.range C ⊆ interior (Set.range (D.ends 0)) ∩
          (Set.range D.square ∪ Set.range D.secondArc)ᶜ ∧
        (∀ z, C z = G
          (⟨1-2*r+r*(z.1:ℝ),by
              constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
           ⟨δ*(z.2:ℝ),by
              constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩)) ∧
        (∀ z, C z ∈ Set.range D.firstArc ↔ (z.2 : ℝ) = 0) ∧
        ∃ c : EndRectangle → Plane, IsEmbedding c ∧
          (∀ z, c z 1 = 0 ↔ (z.2 : ℝ) = 0) ∧
          (∀ z, ∃ v : EndRectangle, D.ends 0 v = C z ∧ c z = Plane.mk v.2 v.1) ∧
          ∃ height : BandWidth → ℝ, Continuous height ∧
            (∀ t, 0 < height t ∧ height t ≤ 1) ∧
            StrictAnti height ∧
            (∀ t : BandWidth,c (t,⟨0,by norm_num⟩)=Plane.mk (height t) 0) ∧
      ∃ s : ℝ, ∃ hs : 0 < s ∧ s ≤ 1/2,
        (∀ x : ℝ, |x| ≤ 2 →
          0 < (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x ∧
          (height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩ +
               height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩)/2 +
            (height ⟨s,by constructor <;> linarith [hs.1,hs.2]⟩ -
               height ⟨-s,by constructor <;> linarith [hs.1,hs.2]⟩)/2*x < 1) ∧
      ∃ q : I → BandWidth, Continuous q ∧ Function.Injective q ∧
        (∀ t : I,(q t:ℝ)=s*(1-2*(t:ℝ))) ∧
      ∃ P : I × BandWidth → Plane, IsEmbedding P ∧
        (∀ z,P z=Plane.mk (c (q z.1,z.2) 0) (4*c (q z.1,z.2) 1)) ∧
      ∃ h : I → ℝ, Continuous h ∧ StrictMono h ∧
        (∀ t,h t=height (q t)) ∧
        (∀ t : I,P (t,⟨0,by norm_num⟩)=Plane.mk (h t) 0) ∧
        (∀ z,P z 1=0 ↔ (z.2:ℝ)=0) ∧
        (∀ x : ℝ, |x| ≤ 2 →
          0 < (h 0+h 1)/2+(h 1-h 0)/2*x ∧
          (h 0+h 1)/2+(h 1-h 0)/2*x < 1) ∧
      ∃ A : I ≃ₜ I,
        (∀ t : I,h (A t)=h 0+(h 1-h 0)*(t:ℝ)) ∧
      ∃ width : ℝ, 0 < width ∧ width ≤ 1 ∧
      ∃ flip : Bool, ∃ H : Plane ≃ₜ Plane,
        (∀ z, z ∉ Plane.openSquare 0 2 → H z=z) ∧
        (∀ x : ℝ,H (Plane.mk x 0)=Plane.mk x 0) ∧
        (∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth,
          (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
          H (Plane.mk (z.val 0) (if flip then -(z.val 1) else z.val 1)) =
            Plane.mk ((2*(P (A t,w) 0-h 0))/(h 1-h 0)-1)
              (P (A t,w) 1)) ∧
      ∃ E : ↥(Plane.closedSquare 0 1) → S, IsEmbedding E ∧
        Set.range E ⊆ Set.range (D.ends 0) ∧
        Disjoint (Set.range E) (Set.range D.square) ∧
        (∀ z, ∃ v : EndRectangle, D.ends 0 v=E z ∧
          (v.1:ℝ)=(z.val 1)/2 ∧ (v.2:ℝ)=((h 0+h 1)/2)+((h 1-h 0)/2)*(2*z.val 0)) ∧
        ∃ F : S ≃ₜ S,
          (∀ x, x ∉ Set.range (D.ends 0) → F x=x) ∧
          (∀ x, x ∈ a.image → F x=x) ∧
          (∀ x, x ∈ b.image → F x=x) ∧
          (∀ x, x ∈ Set.range D.square → F x=x) ∧
  (        ∀ z : ↥(Plane.closedSquare 0 1),
            ∃ w : ↥(Plane.closedSquare 0 1),
              w.val=(1/2:ℝ) • H ((2:ℝ) • z.val) ∧ F (E z)=E w) ∧
      ∀ z : ↥(Plane.closedSquare 0 1), ∃ t : I, ∃ w : BandWidth, ∃ v : EndRectangle,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
        (v.2:ℝ)=(h 0+h 1)/2+(h 1-h 0)/2*z.val 0 ∧
        F (D.ends 0 v)=C (q (A t),w) := by
    apply outsideBandsPackaging_55_source <;> assumption
  have order (height : I → ℝ) (hm : StrictMono height) (A : I ≃ₜ I)
      (hA : ∀ t : I,height (A t)=height 0+(height 1-height 0)*(t:ℝ)) :
      StrictMono A ∧ A 0=0 ∧ A 1=1 := by
    apply outsideBandsPackaging_3581_order <;> assumption
  have parameters (A : I ≃ₜ I) (hAmono : StrictMono A) (s : ℝ) (hs : 0 < s ∧ s ≤ 1/2)
      (r : ℝ) (hr : 0 < r ∧ r < 1/4) :
      ∃ τ : I, 0<τ ∧ τ<1 ∧
        (τ:ℝ)=1-2*r+r*s*(1-2*(A ⟨1/2,by norm_num⟩:ℝ)) ∧
      ∃ c : I, 0<c ∧ c<1 ∧
      ∃ u : I → I,
        (∀ t : I,c≤t → (A (u t):ℝ)=
          (1-(((τ:ℝ)*t-1+2*r)/r)/s)/2) ∧
        (∀ t : I,c≤t → ⟨1/2,by norm_num⟩≤u t) ∧
        (∀ t : I,c≤t → (u t=⟨1/2,by norm_num⟩ ↔ t=1)) ∧
        ∀ t : I,c≤t →
          (τ:ℝ)*t=1-2*r+r*s*(1-2*(A (u t):ℝ)) := by
    apply outsideBandsPackaging_3595_parameters <;> assumption
  have tail {S : Type} [TopologicalSpace S] [T2Space S]
      {a b : Curve S} (D : OneCrossingBandBase a b)
      (y : I) (hy : 0 < y) (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1) :
      ∃ cut : I, 0 < cut ∧ cut < 1 ∧
        ∃ F : I × BandWidth → S, IsEmbedding F ∧
          (∀ w, F (0,w)=D.ends 0
            (⟨δ*w,by constructor <;> nlinarith [w.property.1,w.property.2,hδ.1,hδ.2]⟩,
             ⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩)) ∧
          (∀ w, F (1,w)=D.square (squarePort D.radius D.radius_pos 0 w)) ∧
          (∀ t : I,F (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t)) ∧
          Set.range F ⊆ Set.range (D.ends 0) ∧
          (∀ z, ∃ v : EndRectangle,D.ends 0 v=F z ∧
            (v.1:ℝ)=(δ+(1-δ)*(z.1:ℝ))*(z.2:ℝ) ∧
            (v.2:ℝ) ≤ (y:ℝ) ∧ ((v.2:ℝ)=(y:ℝ) ↔ z.1=0)) ∧
          Set.range F ∩ Set.range D.square =
            Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
          Disjoint (Set.range F) (Set.range D.secondArc) ∧
          (∀ z,F z∈Set.range D.firstArc ↔ (z.2:ℝ)=0) ∧
          D.firstArc cut=D.ends 0 (⟨0,by norm_num⟩,
            ⟨(y:ℝ),by constructor <;> linarith [y.property.1,y.property.2]⟩) := by
    apply outsideBandsPackaging_3690_tail <;> assumption
  have separate {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b)
      (center span : ℝ) (hspan : 0 < span)
      (hcenter : 0 < center ∧ center < 1)
      (E : ↥(Schoenflies.Plane.closedSquare 0 1) → S)
      (hE : ∀ z, ∃ v : EndRectangle,D.ends 0 v=E z ∧
        (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0))
      (T : I × BandWidth → S) (_hT : IsEmbedding T)
      (hcoords : ∀ z, ∃ v : EndRectangle,D.ends 0 v=T z ∧
        (v.2:ℝ)≤center ∧ ((v.2:ℝ)=center ↔ z.1=0))
      (hT0 : ∀ w,T (0,w)=D.ends 0
        (⟨(w:ℝ)/4,by constructor <;> linarith [w.property.1,w.property.2]⟩,
         ⟨center,by constructor <;> linarith [hcenter.1,hcenter.2]⟩)) :
      ∀ z : ↥(Schoenflies.Plane.closedSquare 0 1),0≤z.val 0 →
        |z.val 1|≤1/2 → (E z∈Set.range T ↔ z.val 0=0) := by
    apply outsideBandsPackaging_4045_separate <;> assumption
  have seam {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b)
      (G : I × BandWidth → S) (r δ width : ℝ)
      (hr : 0 < r ∧ r < 1/4) (hδ : 0 < δ ∧ δ ≤ 1) (hw : 0 < width ∧ width ≤ 1)
      (C : EndRectangle → S)
      (hC : ∀ z,C z=G
        (⟨1-2*r+r*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩))
      (q : I → BandWidth) (A : I ≃ₜ I) (F : S ≃ₜ S)
      (flip : Bool) (center span : ℝ)
      (hnative : ∀ z : ↥(Plane.closedSquare 0 1),∃ t : I,∃ w : BandWidth,∃ v : EndRectangle,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
        (v.2:ℝ)=center+span*z.val 0 ∧ F (D.ends 0 v)=C (q (A t),w))
      (T : I × BandWidth → S)
      (hc : 0 < center ∧ center < 1)
      (hT0 : ∀ w,T (0,w)=D.ends 0
        (⟨(w:ℝ)/4,by constructor <;> linarith [w.property.1,w.property.2]⟩,
         ⟨center,⟨by linarith [hc.1],hc.2.le⟩⟩)) :
      ∀ w : BandWidth,F (T (0,flipBandWidth flip w))=
        G (⟨1-2*r+r*(q (A ⟨1/2,by norm_num⟩):ℝ),by
             constructor <;> nlinarith [(q (A ⟨1/2,by norm_num⟩)).property.1,
               (q (A ⟨1/2,by norm_num⟩)).property.2,hr.1,hr.2]⟩,
           ⟨δ*width*(w:ℝ),by
             have hs : 0<δ*width ∧ δ*width≤1 :=
               ⟨mul_pos hδ.1 hw.1,(mul_le_mul_of_nonneg_left hw.2 hδ.1.le).trans (by simpa using hδ.2)⟩
             constructor <;> nlinarith [w.property.1,w.property.2,hs.1,hs.2]⟩) := by
    apply outsideBandsPackaging_4084_seam <;> assumption
  have germ {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b)
      (G : I × BandWidth → S) (r δ width : ℝ)
      (hr : 0 < r ∧ r < 1/4) (hδ : 0 < δ ∧ δ ≤ 1) (hw : 0 < width ∧ width ≤ 1)
      (C : EndRectangle → S)
      (hC : ∀ z,C z=G
        (⟨1-2*r+r*(z.1:ℝ),by constructor <;> nlinarith [z.1.property.1,z.1.property.2,hr.1,hr.2]⟩,
         ⟨δ*(z.2:ℝ),by constructor <;> nlinarith [z.2.property.1,z.2.property.2,hδ.1,hδ.2]⟩))
      (q : I → BandWidth) (A : I ≃ₜ I) (F : S ≃ₜ S)
      (flip : Bool) (center span : ℝ)
      (hnative : ∀ z : ↥(Plane.closedSquare 0 1),∃ t : I,∃ w : BandWidth,∃ v : EndRectangle,
        (t:ℝ)=(z.val 0+1)/2 ∧ (w:ℝ)=width*z.val 1 ∧
        (v.1:ℝ)=(if flip then -(z.val 1) else z.val 1)/4 ∧
        (v.2:ℝ)=center+span*z.val 0 ∧ F (D.ends 0 v)=C (q (A t),w))
      (E : ↥(Plane.closedSquare 0 1) → S)
      (hE : ∀ z,∃ v : EndRectangle,D.ends 0 v=E z ∧
        (v.1:ℝ)=z.val 1/2 ∧ (v.2:ℝ)=center+span*(2*z.val 0))
      (T : I × BandWidth → S)
      (hsep : ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 0 → |z.val 1|≤1/2 →
        (E z∈Set.range T ↔ z.val 0=0))
      (τ c : I) (_hc : 0<c ∧ c<1)
      (u : I → I) (hu : ∀ t : I,c≤t → ⟨1/2,by norm_num⟩≤u t)
      (hu1 : ∀ t : I,c≤t → (u t=⟨1/2,by norm_num⟩ ↔ t=1))
      (hparam : ∀ t : I,c≤t → (τ:ℝ)*t=1-2*r+r*(q (A (u t)):ℝ)) :
      ∀ t : I,c≤t → ∀ w : BandWidth,
        G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
           ⟨δ*width*(w:ℝ),by
             have hs : 0<δ*width ∧ δ*width≤1 :=
               ⟨mul_pos hδ.1 hw.1,(mul_le_mul_of_nonneg_left hw.2 hδ.1.le).trans (by simpa using hδ.2)⟩
             constructor <;> nlinarith [w.property.1,w.property.2,hs.1,hs.2]⟩)
          ∈ F '' Set.range T ↔ t=1 := by
    apply outsideBandsPackaging_4136_germ <;> assumption
  obtain ⟨M,hM0,hM1,G,hG,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,r,δ,hr,hδ,C,hC,hCU,hCformula,haxisC,
    cc,hcc,hccaxis,hccformula,height,hheight,hhb,hmono,hcc0,s,hs,hwindow,
    q,hqc,hqi,hqform,P,hP,hPformula,h,hh,hm,hform,hPc,hPaxis,hphyswindow,
    A,hA,width,hw0,hw1,flip,H,hHfix,hHaxis,hHformula,
    E,hE,hEs,hEq,hEformula,F,hFoutside,hFa,hFb,hFQ,hFE,hnative⟩ := source D
  obtain ⟨hAmono,_,_⟩ := order h hm A hA
  obtain ⟨τ,hτ0,hτ1,hτform,c,hc0,hc1,u,huA,hu,hu1,hparamA⟩ := parameters A hAmono s hs r hr
  have hparam (t : I) (ht : c≤t) : (τ:ℝ)*t=1-2*r+r*(q (A (u t)):ℝ) := by
    rw [hqform]
    simpa only [mul_assoc] using hparamA t ht
  let center := (h 0+h 1)/2
  let span := (h 1-h 0)/2
  have hspan : 0<span := half_pos (sub_pos.mpr (hm (show (0:I)<1 by norm_num)))
  have hcenter : 0<center ∧ center<1 := by simpa [center] using hphyswindow 0 (by norm_num)
  let y : I := ⟨center,⟨by linarith only [hcenter.1],hcenter.2.le⟩⟩
  obtain ⟨cut,hcut0,hcut1,T,hT,hT0,hT1,hTc,hTs,hTcoords,hTQ,hTother,hTaxis,hcutaxis⟩ :=
    tail D y hcenter.1 (1/4) ⟨by norm_num,by norm_num⟩
  have hcutparam : (cut:ℝ)=(M:ℝ)*τ := by
    as_aux_lemma =>
      let z : ↥(Plane.closedSquare 0 1) := ⟨Plane.mk 0 0,by norm_num [Plane.closedSquare,Plane.supDist,Plane.supNorm]⟩
      obtain ⟨t,w,v,ht,hw,hvx,hvy,hn⟩ := hnative z
      have ht' : t=⟨1/2,by norm_num⟩ := Subtype.ext (by simpa [z,Plane.mk] using ht)
      have hw' : w=⟨0,by norm_num⟩ := Subtype.ext (by simpa [z,Plane.mk] using hw)
      have hv0 : (v.1:ℝ)=0 := by cases flip <;> simpa [z,Plane.mk] using hvx
      have hv1 : (v.2:ℝ)=center := by simpa [z,Plane.mk,center] using hvy
      have hva : D.ends 0 v∈a.image := (D.ends_axes 0 v).1.mpr ⟨Or.inl rfl,hv0⟩
      rw [hFa _ hva,ht',hw',hCformula] at hn
      simp only [mul_zero] at hn
      have hcutv : D.ends 0 v=D.firstArc cut := by
        have hv : v=(⟨0,by norm_num⟩,⟨center,by constructor <;> linarith [hcenter.1,hcenter.2]⟩) := by
          apply Prod.ext <;> apply Subtype.ext
          · exact hv0
          · exact hv1
        rw [hv]
        exact hcutaxis.symm
      have htime : 1-2*r+r*(q (A ⟨1/2,by norm_num⟩):ℝ)=(τ:ℝ) := by rw [hqform]; simpa only [mul_assoc] using hτform.symm
      simp_rw [htime] at hn
      let cp : I := ⟨(M:ℝ)*τ,by constructor <;> nlinarith only [M.property.1,M.property.2,τ.property.1,τ.property.2]⟩
      have he : D.firstArc cut=D.firstArc cp := by
        rw [←hcutv,hn,hGc]
        exact D.firstArc.extend_extends' cp
      exact congrArg Subtype.val (D.firstArc_embedded.injective he)
  have hT0' (w : BandWidth) : T (0,w)=D.ends 0
      (⟨(w:ℝ)/4,by constructor <;> linarith [w.property.1,w.property.2]⟩,
       ⟨center,⟨by linarith only [hcenter.1],hcenter.2.le⟩⟩) := by
    as_aux_lemma =>
      rw [hT0]
      congr 1
      apply Prod.ext
      · apply Subtype.ext
        change (1/4:ℝ)*w=(w:ℝ)/4
        ring
      · rfl
  have hTcoord' (z : I × BandWidth) : ∃ v : EndRectangle,D.ends 0 v=T z ∧
      (v.2:ℝ)≤center ∧ ((v.2:ℝ)=center ↔ z.1=0) := by
    obtain ⟨v,hv,_,hvle,hveq⟩ := hTcoords z
    exact ⟨v,hv,hvle,hveq⟩
  have hsep : ∀ z : ↥(Plane.closedSquare 0 1),0≤z.val 0 → |z.val 1|≤1/2 →
      (E z∈Set.range T ↔ z.val 0=0) :=
    separate D center span hspan hcenter E hEformula T hT hTcoord' hT0'
  let J : I × BandWidth → I × BandWidth := fun z => (z.1,flipBandWidth flip z.2)
  have hflip (w : BandWidth) : flipBandWidth flip (flipBandWidth flip w)=w := by
    cases flip <;> apply Subtype.ext <;> simp [flipBandWidth]
  have hJc : Continuous J := by cases flip <;> dsimp [J,flipBandWidth] <;> fun_prop
  have hJi : Function.Injective J := by
    intro z w he
    have hh0 : z.1=w.1 := by simpa only [J] using congrArg (fun v : I × BandWidth => v.1) he
    have hh1 : flipBandWidth flip z.2=flipBandWidth flip w.2 := Prod.mk.inj he |>.2
    apply Prod.ext
    · exact hh0
    simpa only [hflip] using congrArg (flipBandWidth flip) hh1
  let R := F ∘ T ∘ J
  have hR : IsEmbedding R := F.isEmbedding.comp (hT.comp (hJc.isClosedEmbedding hJi).isEmbedding)
  have hRrange : Set.range R=F '' Set.range T := by
    apply Set.Subset.antisymm
    · rintro x ⟨z,rfl⟩; exact Set.mem_image_of_mem F (Set.mem_range_self _)
    · rintro x ⟨v,⟨z,rfl⟩,rfl⟩
      refine ⟨(z.1,flipBandWidth flip z.2),?_⟩
      change F (T (z.1,flipBandWidth flip (flipBandWidth flip z.2)))=F (T z)
      rw [hflip]
  let η := δ*width
  have hη : 0<η ∧ η≤1 := ⟨mul_pos hδ.1 hw0,(mul_le_mul_of_nonneg_left hw1 hδ.1.le).trans (by simpa using hδ.2)⟩
  have hR0 (w : BandWidth) : R (0,w)=G (τ,⟨η*w,by constructor <;> nlinarith only [w.property.1,w.property.2,hη.1,hη.2]⟩) := by
    as_aux_lemma =>
      have hh := seam D G r δ width hr hδ ⟨hw0,hw1⟩ C hCformula q A F flip center span hnative T hcenter hT0' w
      change R (0,w)=_ at hh
      have htime : (⟨1-2*r+r*(q (A ⟨1/2,by norm_num⟩):ℝ),by constructor <;> nlinarith only [(q (A ⟨1/2,by norm_num⟩)).property.1,(q (A ⟨1/2,by norm_num⟩)).property.2,hr.1,hr.2]⟩ : I)=τ := by
        apply Subtype.ext
        change 1-2*r+r*(q (A ⟨1/2,by norm_num⟩):ℝ)=(τ:ℝ)
        rw [hqform]
        simpa only [mul_assoc] using hτform.symm
      rw [htime] at hh
      simpa only [η,mul_assoc] using hh
  refine ⟨M,τ,c,cut,hM0,hM1,hτ0,hτ1,hc0,hc1,hcut0,hcut1,hcutparam,η,hη,flip,G,R,hG,hR,hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,hR0,?_,?_,?_,?_,?_,?_,?_⟩
  · intro w
    change F (T (1,flipBandWidth flip w))=_
    rw [hT1,hFQ _ (Set.mem_range_self _)]
  · intro t
    have hzero : flipBandWidth flip ⟨0,by norm_num⟩=⟨0,by norm_num⟩ := by cases flip <;> apply Subtype.ext <;> simp [flipBandWidth]
    change F (T (t,flipBandWidth flip ⟨0,by norm_num⟩))=_
    rw [hzero,hTc]
    apply hFa
    have hh : D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t)∈Set.range D.firstArc :=
      D.firstArc.extend_range ▸ Set.mem_range_self _
    exact (D.firstArc_range ▸ hh).1
  · intro z
    have hfix (x : S) (hx : x∈Set.range D.firstArc) : F x=x := hFa x (D.firstArc_range ▸ hx).1
    have hm : F (T (J z))∈Set.range D.firstArc ↔ T (J z)∈Set.range D.firstArc := by
      constructor
      · intro hx
        have he : T (J z)=F (T (J z)) := (F.injective (hfix _ hx)).symm
        rw [he]
        exact hx
      · intro hx; rw [hfix _ hx]; exact hx
    change F (T (J z))∈Set.range D.firstArc ↔ (z.2:ℝ)=0
    rw [hm,hTaxis]
    cases flip <;> simp [J,flipBandWidth]
  · apply Set.disjoint_left.mpr
    rintro x ⟨z,rfl⟩ hx
    have hfix := hFb _ (D.secondArc_range ▸ hx).1
    have he : T (J z)=R z := (F.injective hfix).symm
    apply Set.disjoint_left.mp hTother (Set.mem_range_self (J z))
    rw [he]
    exact hx
  · rintro x ⟨z,rfl⟩
    have hv : T (J z)∈Set.range (D.ends 0) := hTs (Set.mem_range_self _)
    by_cases hx : F (T (J z))∈Set.range (D.ends 0)
    · exact hx
    · have hfix := hFoutside _ hx
      have he := F.injective hfix
      exact False.elim (hx (he.symm ▸ hv))
  · ext x
    constructor
    · rintro ⟨hx,hQ⟩
      rw [hRrange] at hx
      obtain ⟨v,hv,hve⟩ := hx
      have hfix : F x=x := hFQ x hQ
      have he : v=x := F.injective (hve.trans hfix.symm)
      exact hTQ ▸ ⟨he ▸ hv,hQ⟩
    · intro hx
      have hh := hTQ.symm ▸ hx
      refine ⟨?_,hh.2⟩
      rw [hRrange]
      exact ⟨x,hh.1,hFQ x hh.2⟩
  · intro t ht w
    rw [hRrange]
    have hh := germ D G r δ width hr hδ ⟨hw0,hw1⟩ C hCformula q A F flip center span hnative E hEformula T hsep τ c ⟨hc0,hc1⟩ u hu hu1 hparam t ht w
    simpa [η,mul_assoc] using hh

private theorem outsideBandsPackaging_21_firstBand {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
    {a b : Curve S} (D : OneCrossingBandBase a b) :
    ∃ flip : Bool,∃ B : I × BandWidth → S,IsEmbedding B ∧
      (∀ t : I,B (t,⟨0,by norm_num⟩)=D.firstArc t) ∧
      (∀ w,B (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
      (∀ w,B (1,w)=D.square (squarePort D.radius D.radius_pos 0 (flipBandWidth flip w))) ∧
      Disjoint (Set.range B) (Set.range D.secondArc) ∧
      Disjoint (Set.range B) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
      Set.range B ∩ Set.range D.square=
        Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∪
        Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) := by
  have align {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ M τ c cut : I, 0<M ∧ M<1 ∧ 0<τ ∧ τ<1 ∧ 0<c ∧ c<1 ∧
        0<cut ∧ cut<1 ∧ (cut:ℝ)=(M:ℝ)*τ ∧
      ∃ η : ℝ,∃ hη : 0<η ∧ η≤1,
      ∃ flip : Bool,∃ G R : I × BandWidth → S,
        IsEmbedding G ∧ IsEmbedding R ∧
        (∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t)) ∧
        Set.range G ∩ Set.range D.firstArc=D.firstArc '' Icc 0 M ∧
        Set.range G ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        Disjoint (Set.range G) (Set.range D.secondArc) ∧
        Disjoint (Set.range G) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
        (∀ w,R (0,w)=G (τ,⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)) ∧
        (∀ w,R (1,w)=D.square (squarePort D.radius D.radius_pos 0 (flipBandWidth flip w))) ∧
        (∀ t : I,R (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t)) ∧
        (∀ z,R z∈Set.range D.firstArc ↔ (z.2:ℝ)=0) ∧
        Disjoint (Set.range R) (Set.range D.secondArc) ∧
        Set.range R ⊆ Set.range (D.ends 0) ∧
        Set.range R ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) ∧
        ∀ t : I,c≤t → ∀ w : BandWidth,
          G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
             ⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)∈Set.range R ↔ t=1 := by
    apply outsideBandsPackaging_32_align <;> assumption
  have core {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b)
      (G R : I × BandWidth → S) (M τ cut : I)
      (hcut : 0<cut ∧ cut<1) (hcutparam : (cut:ℝ)=(M:ℝ)*τ)
      (hGc : ∀ t : I,G (t,⟨0,by norm_num⟩)=D.firstArc.extend ((M:ℝ)*t))
      (hRc : ∀ t : I,R (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)+(1-(cut:ℝ))*t))
      (hRaxis : ∀ z,R z∈Set.range D.firstArc ↔ (z.2:ℝ)=0)
      (hRsource : Set.range R ∩ Set.range D.square=Set.range
        (fun w => D.square (squarePort D.radius D.radius_pos 0 w)))
      (hG0 : ∀ w,G (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) :
      (∀ t : I,t<1 → G
        (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
         ⟨0,by norm_num⟩)∉Set.range R) ∧
      (∀ w,G (0,w)∉Set.range R) := by
    apply outsideBandsPackaging_4370_core <;> assumption
  have narrow {S : Type} [TopologicalSpace S] [T2Space S]
      (G R : I × BandWidth → S) (hG : IsEmbedding G) (hR : IsEmbedding R)
      (τ c : I) (hτ : 0<τ) (hc : 0<c ∧ c<1)
      (η : ℝ) (hη : 0<η ∧ η≤1)
      (hseam : ∀ w,R (0,w)=G (τ,⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩))
      (hcore : ∀ t : I,t<1 → G
        (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
         ⟨0,by norm_num⟩)∉Set.range R)
      (hbottom : ∀ w,G (0,w)∉Set.range R)
      (hgerm : ∀ t : I,c≤t → ∀ w : BandWidth,
        G (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
           ⟨η*w,by constructor <;> nlinarith [w.property.1,w.property.2,hη.1,hη.2]⟩)∈Set.range R ↔ t=1) :
      ∃ L : I × BandWidth → S,IsEmbedding L ∧
        (∀ w,L (0,w)=G (0,w)) ∧ (∀ w,L (1,w)=R (0,w)) ∧
        (∀ t : I,L (t,⟨0,by norm_num⟩)=G
          (⟨(τ:ℝ)*t,by constructor <;> nlinarith [τ.property.1,τ.property.2,t.property.1,t.property.2]⟩,
           ⟨0,by norm_num⟩)) ∧
        Set.range L ⊆ Set.range G ∧
        Set.range L ∩ Set.range R=Set.range (fun w => R (0,w)) ∧
        ∃ scale : I → ℝ,Continuous scale ∧ (∀ t,0<scale t ∧ scale t≤1) ∧
          ∀ z,∃ t : I,∃ w : BandWidth,(t:ℝ)=(τ:ℝ)*z.1 ∧
            (w:ℝ)=scale z.1*z.2 ∧ L z=G (t,w) := by
    apply outsideBandsPackaging_4420_narrow <;> assumption
  have axis {S : Type} [TopologicalSpace S] {x y : S}
      (p : Path x y) (G : I × BandWidth → S) (hG : IsEmbedding G)
      (M : I) (hM : 0<M)
      (hGc : ∀ t : I,G (t,⟨0,by norm_num⟩)=p.extend ((M:ℝ)*t))
      (hGmeet : Set.range G ∩ Set.range p=p '' Icc 0 M) :
      ∀ z,G z∈Set.range p ↔ (z.2:ℝ)=0 := by
    apply outsideBandsPackaging_4667_axis <;> assumption
  have paste {S : Type} [TopologicalSpace S] [T2Space S]
      {x y : S} (p : Path x y) (hp : IsEmbedding p)
      (L R : I × BandWidth → S) (hL : IsEmbedding L) (hR : IsEmbedding R)
      (hseam : ∀ w,L (1,w)=R (0,w))
      (hmeet : Set.range L ∩ Set.range R=Set.range (fun w => L (1,w)))
      (haxisL : ∀ z,L z∈Set.range p ↔ (z.2:ℝ)=0)
      (haxisR : ∀ z,R z∈Set.range p ↔ (z.2:ℝ)=0)
      (hcover : Set.range p ⊆ Set.range L ∪ Set.range R)
      (hstart : L (0,⟨0,by norm_num⟩)=p 0)
      (hend : R (1,⟨0,by norm_num⟩)=p 1) :
      ∃ G : I × BandWidth → S,IsEmbedding G ∧
        (∀ t : I,G (t,⟨0,by norm_num⟩)=p t) ∧
        (∀ w,G (0,w)=L (0,w)) ∧ (∀ w,G (1,w)=R (1,w)) ∧
        Set.range G=Set.range L ∪ Set.range R ∧
        ∀ z,G z∈Set.range p ↔ (z.2:ℝ)=0 := by
    apply outsideBandsPackaging_4690_paste <;> assumption
  obtain ⟨M,τ,c,cut,hM0,hM1,hτ0,hτ1,hc0,hc1,hcut0,hcut1,hcutparam,η,hη,flip,G,R,hG,hR,
    hG0,hGc,hGmeet,hGQ,hGother,hGavoidK,hR0,hR1,hRc,hRaxis,hRother,hRs,hRQ,hgerm⟩ := align D
  obtain ⟨hcore,hbottom⟩ := core D G R M τ cut ⟨hcut0,hcut1⟩ hcutparam hGc hRc hRaxis hRQ hG0
  obtain ⟨L,hL,hL0,hL1,hLc,hLs,hLR,scale,hsc,hs,hwidth⟩ :=
    narrow G R hG hR τ c hτ0 ⟨hc0,hc1⟩ η hη hR0 hcore hbottom hgerm
  have hGaxis := axis D.firstArc G hG M hM0 hGc hGmeet
  have hLaxis (z : I × BandWidth) : L z∈Set.range D.firstArc ↔ (z.2:ℝ)=0 := by
    obtain ⟨t,w,ht,hw,hLw⟩ := hwidth z
    rw [hLw,hGaxis]
    change (w:ℝ)=0 ↔ (z.2:ℝ)=0
    rw [hw,mul_eq_zero]
    simp [(hs z.1).1.ne']
  have hLc' (t : I) : L (t,⟨0,by norm_num⟩)=D.firstArc.extend ((cut:ℝ)*t) := by
    rw [hLc,hGc]
    congr 1
    change (M:ℝ)*((τ:ℝ)*t)=(cut:ℝ)*t
    rw [←mul_assoc,hcutparam]
  have hcover : Set.range D.firstArc⊆Set.range L ∪ Set.range R := by
    as_aux_lemma =>
      rintro x ⟨t,rfl⟩
      by_cases ht : t≤cut
      · let u : I := ⟨(t:ℝ)/(cut:ℝ),⟨div_nonneg t.property.1 (show 0≤(cut:ℝ) from hcut0.le),
          (div_le_one (show 0<(cut:ℝ) from hcut0)).mpr ht⟩⟩
        refine Or.inl ⟨(u,⟨0,by norm_num⟩),?_⟩
        rw [hLc']
        have he : (cut:ℝ)*(u:ℝ)=(t:ℝ) := by dsimp [u]; field_simp [ne_of_gt (show 0<(cut:ℝ) from hcut0)]
        rw [he,Path.extend_extends']
      · let u : I := ⟨((t:ℝ)-cut)/(1-(cut:ℝ)),by
          have hden : 0<1-(cut:ℝ) := sub_pos.mpr hcut1
          constructor
          · exact div_nonneg (sub_nonneg.mpr (le_of_not_ge ht)) hden.le
          · apply (div_le_one hden).mpr
            linarith [t.property.2]⟩
        refine Or.inr ⟨(u,⟨0,by norm_num⟩),?_⟩
        rw [hRc]
        have he : (cut:ℝ)+(1-(cut:ℝ))*(u:ℝ)=(t:ℝ) := by
          dsimp [u]
          field_simp [ne_of_gt (sub_pos.mpr (show (cut:ℝ)<1 from hcut1))]
          ring
        rw [he,Path.extend_extends']
  have hstart : L (0,⟨0,by norm_num⟩)=D.firstArc 0 := by rw [hLc']; simp
  have hend : R (1,⟨0,by norm_num⟩)=D.firstArc 1 := by rw [hRc]; simp
  have hseam (w : BandWidth) : L (1,w)=R (0,w) := hL1 w
  have hLR' : Set.range L ∩ Set.range R=Set.range (fun w => L (1,w)) := by
    rw [hLR]
    congr 1
    funext w
    exact (hL1 w).symm
  obtain ⟨B,hB,hBc,hB0,hB1,hBrange,_⟩ :=
    paste D.firstArc D.firstArc_embedded L R hL hR hseam hLR' hLaxis hRaxis hcover hstart hend
  have hLQ : Set.range L ∩ Set.range D.square=Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) := by
    apply Set.Subset.antisymm
    · rintro x ⟨hx,hQ⟩
      exact hGQ ▸ ⟨hLs hx,hQ⟩
    · rintro x ⟨w,rfl⟩
      exact ⟨⟨(0,w),(hL0 w).trans (hG0 w)⟩,Set.mem_range_self _⟩
  refine ⟨flip,B,hB,hBc,fun w => (hB0 w).trans ((hL0 w).trans (hG0 w)),
    fun w => (hB1 w).trans (hR1 w),?_,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hBrange] at hx
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hGother (hLs hx) hy
    · exact Set.disjoint_left.mp hRother hx hy
  · apply Set.disjoint_left.mpr
    intro x hx hy
    rw [hBrange] at hx
    rcases hx with hx | hx
    · exact Set.disjoint_left.mp hGavoidK (hLs hx) hy
    · rcases hy with h1 | h3
      · exact Set.disjoint_left.mp (D.ends_disjoint (show (0:Fin 4)≠1 by decide)) (hRs hx) h1
      · exact Set.disjoint_left.mp (D.ends_disjoint (show (0:Fin 4)≠3 by decide)) (hRs hx) h3
  · rw [hBrange,Set.union_inter_distrib_right,hLQ,hRQ]


theorem exists_actual_unoriented_outside_bands {S : Type} [TopologicalSpace S] [T2Space S]
    [ChartedSpace Schoenflies.Plane S] {a b : Curve S}
    (D : OneCrossingBandBase a b) : Nonempty (UnorientedOutsideBands D) := by
  have firstBand {S : Type} [TopologicalSpace S] [T2Space S] [ChartedSpace Plane S]
      {a b : Curve S} (D : OneCrossingBandBase a b) :
      ∃ flip : Bool,∃ B : I × BandWidth → S,IsEmbedding B ∧
        (∀ t : I,B (t,⟨0,by norm_num⟩)=D.firstArc t) ∧
        (∀ w,B (0,w)=D.square (squarePort D.radius D.radius_pos 2 w)) ∧
        (∀ w,B (1,w)=D.square (squarePort D.radius D.radius_pos 0 (flipBandWidth flip w))) ∧
        Disjoint (Set.range B) (Set.range D.secondArc) ∧
        Disjoint (Set.range B) (Set.range (D.ends 1) ∪ Set.range (D.ends 3)) ∧
        Set.range B ∩ Set.range D.square=
          Set.range (fun w => D.square (squarePort D.radius D.radius_pos 2 w)) ∪
          Set.range (fun w => D.square (squarePort D.radius D.radius_pos 0 w)) := by
    apply outsideBandsPackaging_21_firstBand <;> assumption
  have swapBase {S : Type} [TopologicalSpace S] {a b : Curve S}
      (D : OneCrossingBandBase a b) :
      ∃ E : OneCrossingBandBase b a,
        (∀ t,E.firstArc t=D.secondArc t) ∧
        (∀ t,E.secondArc t=D.firstArc t) ∧
        (∀ w,E.square (squarePort E.radius E.radius_pos 2 w)=D.square (squarePort D.radius D.radius_pos 3 w)) ∧
        (∀ w,E.square (squarePort E.radius E.radius_pos 0 w)=D.square (squarePort D.radius D.radius_pos 1 w)) ∧
        Set.range E.square=Set.range D.square ∧
        Set.range (E.ends 1) ∪ Set.range (E.ends 3)=Set.range (D.ends 0) ∪ Set.range (D.ends 2) := by
    apply outsideBandsPackaging_4882_swapBase <;> assumption
  have taper {S : Type} [TopologicalSpace S] [T2Space S]
      (E : I × BandWidth → S) (hE : IsEmbedding E)
      (K : Set S) (hK : IsClosed K)
      (hcenter : ∀ t : I,E (t,⟨0,by norm_num⟩)∉K)
      (hbottom : ∀ w : BandWidth,E (0,w)∉K)
      (htop : ∀ w : BandWidth,E (1,w)∉K) :
      ∃ F : I × BandWidth → S, IsEmbedding F ∧
        (∀ t,F (t,⟨0,by norm_num⟩)=E (t,⟨0,by norm_num⟩)) ∧
        (∀ w,F (0,w)=E (0,w)) ∧ (∀ w,F (1,w)=E (1,w)) ∧
        Set.range F ⊆ Set.range E ∧ Disjoint (Set.range F) K := by
    apply outsideBandsPackaging_4966_taper <;> assumption
  obtain ⟨flip,B,hB,hBc,hB0,hB1,hBother,hBends,hBQ⟩ := firstBand D
  obtain ⟨E,hEfirst,hEsecond,hE2,hE0,hEQ,hEends⟩ := swapBase D
  obtain ⟨flip2,C,hC,hCc,hC0,hC1,hCother,hCends,hCQ⟩ := firstBand E
  have hC0' (w : BandWidth) : C (0,w)=D.square (squarePort D.radius D.radius_pos 3 w) := (hC0 w).trans (hE2 w)
  have hC1' (w : BandWidth) : C (1,w)=D.square (squarePort D.radius D.radius_pos 1 (flipBandWidth flip2 w)) := (hC1 w).trans (hE0 _)
  have hK : IsClosed (Set.range B) := isCompact_range hB.continuous |>.isClosed
  have hcenter (t : I) : C (t,⟨0,by norm_num⟩)∉Set.range B := by
    rw [hCc,hEfirst]
    intro hx
    exact Set.disjoint_left.mp hBother hx (Set.mem_range_self t)
  have hbottom (w : BandWidth) : C (0,w)∉Set.range B := by
    rw [hC0',←D.ends_seam 3]
    intro hx
    exact Set.disjoint_left.mp hBends hx (Or.inr (Set.mem_range_self _))
  have htop (w : BandWidth) : C (1,w)∉Set.range B := by
    rw [hC1',←D.ends_seam 1]
    intro hx
    exact Set.disjoint_left.mp hBends hx (Or.inl (Set.mem_range_self _))
  obtain ⟨F,hF,hFc,hF0,hF1,hsubset,hdisjoint⟩ := taper C hC (Set.range B) hK hcenter hbottom htop
  have hF0' (w : BandWidth) : F (0,w)=D.square (squarePort D.radius D.radius_pos 3 w) := (hF0 w).trans (hC0' w)
  have hF1' (w : BandWidth) : F (1,w)=D.square (squarePort D.radius D.radius_pos 1 (flipBandWidth flip2 w)) := (hF1 w).trans (hC1' w)
  have hflip (w : BandWidth) : flipBandWidth flip2 (flipBandWidth flip2 w)=w := by
    cases flip2 <;> apply Subtype.ext <;> simp [flipBandWidth]
  have hFQ : Set.range F ∩ Set.range D.square=
      Set.range (fun w => D.square (squarePort D.radius D.radius_pos 3 w)) ∪
      Set.range (fun w => D.square (squarePort D.radius D.radius_pos 1 w)) := by
    as_aux_lemma =>
      have hCQ' : Set.range C ∩ Set.range D.square=
          Set.range (fun w => D.square (squarePort D.radius D.radius_pos 3 w)) ∪
          Set.range (fun w => D.square (squarePort D.radius D.radius_pos 1 w)) := by
        rw [←hEQ,hCQ]
        congr 1 <;> congr 1 <;> funext w
        · exact hE2 w
        · exact hE0 w
      ext x
      constructor
      · rintro ⟨hx,hq⟩
        exact hCQ' ▸ (show x∈Set.range C ∩ Set.range D.square from ⟨hsubset hx,hq⟩)
      · rintro (⟨w,rfl⟩|⟨w,rfl⟩)
        · exact ⟨⟨(0,w),hF0' w⟩,Set.mem_range_self _⟩
        · refine ⟨⟨(1,flipBandWidth flip2 w),?_⟩,Set.mem_range_self _⟩
          rw [hF1',hflip]
  exact ⟨{
    firstFlip := flip
    secondFlip := flip2
    first := B
    second := F
    first_embedded := hB
    second_embedded := hF
    first_center := hBc
    second_center := fun t => (hFc t).trans ((hCc t).trans (hEfirst t))
    first_bottom := hB0
    first_top := hB1
    second_left := hF0'
    second_right := hF1'
    bands_disjoint := hdisjoint.symm
    first_square := hBQ
    second_square := hFQ
  }⟩
end CurveComplex

#print axioms CurveComplex.exists_actual_unoriented_outside_bands
