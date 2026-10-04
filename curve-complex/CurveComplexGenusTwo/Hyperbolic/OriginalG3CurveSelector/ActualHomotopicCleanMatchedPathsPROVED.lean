import CurveComplexGenusTwo.Topology.ActualSourceGeometry.ActualTopologicalUniversalCoverPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualComponentHyperbolicDevelopmentPROVED
import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualDeckDevelopmentIsometryPROVED
import CurveComplexGenusTwo.Hyperbolic.CompactSegmentParametrization
import CurveComplexGenusTwo.Hyperbolic.OriginalG3CurveSelector.PeriodicH2CleanMatchedContactsPROVED
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Foundations.ActualIntersectionBridge
import Mathlib.Order.ConditionallyCompleteLattice.Finset
set_option maxHeartbeats 4000000
namespace CurveComplex.Hyperbolic
open Set Topology
private def actual_conjugated_cover_action
    {G E F : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace F] (h : F ≃ₜ E) : MulAction G F :=
{
    smul := fun g x => h.symm (g • h x)
    one_smul := fun x => by
      change h.symm ((1 : G) • h x) = x
      simp
    mul_smul := fun g k x => by
      change h.symm ((g * k) • h x) = h.symm (g • h (h.symm (k • h x)))
      simp [mul_smul] }
private theorem actual_cover_with_conjugated_action
    {G E F S : Type*} [Group G] [TopologicalSpace E] [MulAction G E]
    [TopologicalSpace F] [TopologicalSpace S]
    (p : E → S) (hp : IsQuotientCoveringMap p G) (h : F ≃ₜ E) :
    letI := actual_conjugated_cover_action (G := G) h
    IsQuotientCoveringMap (p ∘ h : F → S) G := by
  letI := actual_conjugated_cover_action (G := G) h
  refine { hp.toIsQuotientMap.comp h.isQuotientMap with
    continuous_const_smul := ?_
    apply_eq_iff_mem_orbit := ?_
    disjoint := ?_ }
  · intro g
    change Continuous (fun x : F => h.symm (g • h x))
    exact h.symm.continuous.comp ((hp.continuous_const_smul g).comp h.continuous)
  · intro x y
    change p (h x) = p (h y) ↔ ∃ g : G, h.symm (g • h y) = x
    rw [hp.apply_eq_iff_mem_orbit]
    constructor
    · rintro ⟨g,hg⟩
      change g • h y = h x at hg
      exact ⟨g,by rw [hg,h.symm_apply_apply]⟩
    · rintro ⟨g,hg⟩
      refine ⟨g,?_⟩
      exact (h.symm_apply_eq.mp hg)
  · intro x
    obtain ⟨U,hU,hdis⟩ := hp.disjoint (h x)
    refine ⟨h ⁻¹' U,h.continuous.continuousAt.preimage_mem_nhds hU,?_⟩
    intro g hg
    apply hdis g
    obtain ⟨y,⟨z,hz,rfl⟩,hy⟩ := hg
    refine ⟨h (g • z),⟨h z,hz,?_⟩,hy⟩
    change g • h z = h (h.symm (g • h z))
    simp
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology
private theorem periodic_contact_data_produces_matched_paths
    {X G : Type} [TopologicalSpace X] [T2Space X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (F J : C(ℝ,H2))
    (hF : ∀ s : ℝ, q (F s) = a.map (Circle.exp s))
    (hJ : ∀ s : ℝ, q (J s) = b.map (Circle.exp s))
    (r s t v : ℝ) (hrs : r < s) (hwidth : s-r < 2*Real.pi)
    (htv : t ≠ v) (hwidthJ : |v-t| < 2*Real.pi) (k : G)
    (hleft : F r = k • J t) (hright : F s = k • J v)
    (hclean : ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image) :
    ∃ u z : X, u ≠ z ∧ ∃ f g : Path u z,
      IsEmbedding f ∧ IsEmbedding g ∧ Set.range f ⊆ a.image ∧
      Set.range g ⊆ b.image ∧
      f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.imageᶜ ∧ f.Homotopic g := by
  let A : Path (F r) (F s) := {
    toFun := fun u => F (r+(s-r)*u.val)
    continuous_toFun := by fun_prop
    source' := by simp
    target' := by simp }
  let B₀ : Path (k • J t) (k • J v) := {
    toFun := fun u => k • J (t+(v-t)*u.val)
    continuous_toFun := (hdeck k).continuous.comp (J.continuous.comp (by fun_prop))
    source' := by simp
    target' := by simp }
  let B : Path (F r) (F s) := B₀.cast hleft hright
  let f := A.map hq.continuous
  let g := B.map hq.continuous
  have injF : Function.Injective f := by
    intro u w he
    have hecircle : Circle.exp (r+(s-r)*u.val)=Circle.exp (r+(s-r)*w.val) := by
      apply a.embedded.injective
      simpa [f,A,hF] using he
    have hi (x : CurveComplex.Interval) : r+(s-r)*x.val ∈ Set.Icc r s := by
      constructor <;> nlinarith [x.property.1,x.property.2]
    have h := Circle.exp_injOn_Icc hwidth (hi u) (hi w) hecircle
    apply Subtype.ext
    nlinarith
  have injG : Function.Injective g := by
    intro u w he
    have hecircle : Circle.exp (t+(v-t)*u.val)=Circle.exp (t+(v-t)*w.val) := by
      apply b.embedded.injective
      simpa [g,B,B₀,hq.map_smul,hJ] using he
    have hi (x : CurveComplex.Interval) : t+(v-t)*x.val ∈ Set.Icc (min t v) (max t v) := by
      rcases le_total t v with h | h
      · rw [min_eq_left h,max_eq_right h]
        constructor <;> nlinarith [x.property.1,x.property.2]
      · rw [min_eq_right h,max_eq_left h]
        constructor <;> nlinarith [x.property.1,x.property.2]
    have hw : max t v-min t v < 2*Real.pi := by
      simpa only [max_sub_min_eq_abs,abs_sub_comm] using hwidthJ
    have h := Circle.exp_injOn_Icc hw (hi u) (hi w) hecircle
    apply Subtype.ext
    have hdiff : v-t ≠ 0 := sub_ne_zero.mpr htv.symm
    exact mul_left_cancel₀ hdiff (by linarith)
  have hf := (f.continuous.isClosedEmbedding injF).isEmbedding
  have hg := (g.continuous.isClosedEmbedding injG).isEmbedding
  refine ⟨q (F r),q (F s),?_,f,g,hf,hg,?_,?_,?_,?_⟩
  · intro h
    have hh : f 0=f 1 := f.source.trans (h.trans f.target.symm)
    have := injF hh
    exact (zero_ne_one : (0 : CurveComplex.Interval) ≠ 1) this
  · rintro x ⟨u,rfl⟩
    change q (F (r+(s-r)*u.val)) ∈ a.image
    rw [hF]
    exact Set.mem_range_self _
  · rintro x ⟨u,rfl⟩
    change q (k • J (t+(v-t)*u.val)) ∈ b.image
    rw [hq.map_smul,hJ]
    exact Set.mem_range_self _
  · rintro x ⟨u,hu,rfl⟩
    apply hclean
    constructor <;> change _ < _ <;>
      nlinarith [show 0 < u.val from hu.1,show u.val < 1 from hu.2]
  · exact (SimplyConnectedSpace.paths_homotopic A B).map ⟨q,hq.continuous⟩


private theorem periodic_original_lifts_produce_actual_clean_matched_paths
    {X G : Type} [TopologicalSpace X] [T2Space X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b)
    (hcount : 2 ≤ (a.image ∩ b.image).ncard)
    (F J : C(ℝ,H2)) (g : G) (ε : ℝ) (hε : 0 < ε)
    (hdisplacement : ∀ z : H2, ε ≤ dist z (g • z))
    (hF : ∀ s : ℝ, q (F s) = a.map (Circle.exp s))
    (hJ : ∀ s : ℝ, q (J s) = b.map (Circle.exp s))
    (hFperiod : ∀ s : ℝ, F (s+2*Real.pi) = g • F s)
    (hJperiod : ∀ s : ℝ, J (s+2*Real.pi) = g • J s) :
    ∃ u z : X, u ≠ z ∧ ∃ f g : Path u z,
      IsEmbedding f ∧ IsEmbedding g ∧ Set.range f ⊆ a.image ∧
      Set.range g ⊆ b.image ∧
      f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.imageᶜ ∧ f.Homotopic g := by
  obtain ⟨r,s,t,v,hrs,hwidth,htv,hwidthJ,k,hr,hs,hclean⟩ :=
    periodic_actual_h2_lifts_have_clean_matched_contacts q hq hdeck a b ht hcount F J g
      ε hε hdisplacement hF hJ hFperiod hJperiod
  exact periodic_contact_data_produces_matched_paths q hq hdeck a b F J hF hJ
    r s t v hrs hwidth htv hwidthJ k hr hs hclean
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology
private theorem actual_metric_path_segment (x y : H2) :
    ∃ γ : Path x y, ∀ s t : unitInterval,
      dist (γ s) (γ t)=dist x y * dist (s : ℝ) (t : ℝ) := by
  obtain ⟨e,hx,hy⟩ := exists_pair_vertical_isometry x y
  let α := Real.log (e x).im
  let β := Real.log (e y).im
  have hvx : verticalPath α=e x := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hx.symm
    · simpa [verticalPath,α] using Real.exp_log (e x).im_pos
  have hvy : verticalPath β=e y := by
    apply UpperHalfPlane.ext_re_im
    · simpa [verticalPath] using hy.symm
    · simpa [verticalPath,β] using Real.exp_log (e y).im_pos
  let γ : Path x y := {
    toFun := fun t => e.symm (verticalPath (α+(β-α)*t.val))
    continuous_toFun := e.symm.continuous.comp
      (verticalPath_isometry.continuous.comp (continuous_const.add
        (continuous_const.mul continuous_subtype_val)))
    source' := by simp [hvx]
    target' := by simpa [hvy] }
  have hd : dist x y=|β-α| := by
    rw [←e.isometry.dist_eq,←hvx,←hvy,verticalPath_isometry.dist_eq,Real.dist_eq,abs_sub_comm]
  refine ⟨γ,?_⟩
  intro s t
  change dist (e.symm (verticalPath (α+(β-α)*s.val)))
    (e.symm (verticalPath (α+(β-α)*t.val)))=_
  rw [e.symm.isometry.dist_eq,verticalPath_isometry.dist_eq,Real.dist_eq,hd,Real.dist_eq]
  have he : α+(β-α)*s.val-(α+(β-α)*t.val)=(β-α)*(s.val-t.val) := by ring
  rw [he,abs_mul]
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology CurveComplex.LocalSurgery
private theorem actual_cover_crossing_chart
    {P X : Type} [TopologicalSpace P] [TopologicalSpace X]
    (q : P → X) (hq : IsLocalHomeomorph q) (a b : Curve X) (z : P)
    (hc : CrossesAt a b (q z)) :
    ∃ K : OpenPartialHomeomorph P (ℝ × ℝ), z ∈ K.source ∧ K z = (0,0) ∧
      ∀ x ∈ K.source,
        (q x ∈ a.image ↔ (K x).1=0) ∧ (q x ∈ b.image ↔ (K x).2=0) := by
  classical
  obtain ⟨U,V,hzU,h,hU,hV,hzero,haxes⟩ := hc
  let C := crossingPartialChart U V hU hV ⟨q z,hzU⟩ h
  have hCs : C.source=U := by simp [C,crossingPartialChart]
  have hCval (x : X) (hx : x ∈ U) : C x = (h ⟨x,hx⟩ : ℝ × ℝ) := by
    simp only [C,crossingPartialChart,OpenPartialHomeomorph.trans_apply,
      Homeomorph.toOpenPartialHomeomorph_apply]
    change (h (((⟨U,hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe
      ⟨⟨q z,hzU⟩⟩).symm x) : ℝ × ℝ) = (h ⟨x,hx⟩ : ℝ × ℝ)
    have hinv := ((⟨U,hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe
      ⟨⟨q z,hzU⟩⟩).left_inv (show (⟨x,hx⟩ : U) ∈ Set.univ from trivial)
    change ((⟨U,hU⟩ : TopologicalSpace.Opens X).openPartialHomeomorphSubtypeCoe
      ⟨⟨q z,hzU⟩⟩).symm x=⟨x,hx⟩ at hinv
    rw [hinv]
  obtain ⟨e,hze,he⟩ := hq z
  let K := e.trans C
  have hzK : z ∈ K.source := by
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨hze,?_⟩
    rw [←he,hCs]
    exact hzU
  refine ⟨K,hzK,?_,?_⟩
  · change C (e z)=(0,0)
    rw [←he,hCval _ hzU]
    exact hzero
  · intro x hx
    have hxC : e x ∈ C.source := hx.2
    have hxU : q x ∈ U := by rw [he]; exact hCs ▸ hxC
    change (q x ∈ a.image ↔ (C (e x)).1=0) ∧ (q x ∈ b.image ↔ (C (e x)).2=0)
    rw [←he,hCval _ hxU]
    exact haxes (q x) hxU


private theorem actual_open_subtype_curves_retain_transverse_count
    {E : Type} [TopologicalSpace E] (A : Set E) (hA : IsOpen A)
    (a b : Curve E) (a' b' : Curve A)
    (ha' : ∀ z, (a'.map z).val=a.map z)
    (hb' : ∀ z, (b'.map z).val=b.map z)
    (ht : Transverse a b) (hcount : 2≤(a.image ∩ b.image).ncard) :
    Transverse a' b' ∧ 2≤(a'.image ∩ b'.image).ncard := by
  have haimage (z : A) : z ∈ a'.image ↔ z.val ∈ a.image := by
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨w,(ha' w).symm⟩
    · rintro ⟨w,hw⟩
      exact ⟨w,Subtype.ext ((ha' w).trans hw)⟩
  have hbimage (z : A) : z ∈ b'.image ↔ z.val ∈ b.image := by
    constructor
    · rintro ⟨w,rfl⟩
      exact ⟨w,(hb' w).symm⟩
    · rintro ⟨w,hw⟩
      exact ⟨w,Subtype.ext ((hb' w).trans hw)⟩
  have hinter : a'.image ∩ b'.image=Subtype.val ⁻¹' (a.image ∩ b.image) := by
    ext z
    exact and_congr (haimage z) (hbimage z)
  constructor
  · constructor
    · rw [hinter]
      exact ht.1.preimage Subtype.val_injective.injOn
    · intro z hz
      have hz' : z.val ∈ a.image ∩ b.image := ⟨(haimage z).mp hz.1,(hbimage z).mp hz.2⟩
      obtain ⟨K,hzK,hzero,haxes⟩ := actual_cover_crossing_chart Subtype.val
        hA.isOpenEmbedding_subtypeVal.isLocalHomeomorph a b z (ht.2 _ hz')
      refine ⟨K.source,K.target,hzK,K.toHomeomorphSourceTarget,K.open_source,K.open_target,hzero,?_⟩
      intro x hx
      exact ⟨(haimage x).trans (haxes x hx).1,(hbimage x).trans (haxes x hx).2⟩
  · rw [hinter,Set.ncard_preimage_of_injective_subset_range Subtype.val_injective]
    · exact hcount
    · rintro z ⟨⟨w,hw⟩,hz⟩
      exact ⟨a'.map w,(ha' w).trans hw⟩
end CurveComplex.Hyperbolic


namespace CurveComplex.Hyperbolic
open Topology Set

private theorem first_contact_embedded_path
    {X : Type} [TopologicalSpace X] [T2Space X]
    {u v : X} (f : Path u v) (hf : IsEmbedding f) (A B : Set X)
    (hA : Set.range f ⊆ A) (hfinite : (A ∩ B).Finite) (hv : v ∈ B) :
    ∃ z : X, u ≠ z ∧ ∃ p : Path u z, IsEmbedding p ∧
      Set.range p ⊆ A ∧ p '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ Bᶜ ∧ z ∈ B := by
  classical
  let S : Set CurveComplex.Interval := {t | 0 < t ∧ f t ∈ B}
  have hSfinite : S.Finite := by
    apply (hfinite.preimage hf.injective.injOn).subset
    intro t ht
    exact ⟨hA (Set.mem_range_self t),ht.2⟩
  have hSnonempty : S.Nonempty := ⟨1,by simpa [S] using hv⟩
  let τ := sInf S
  obtain ⟨hτ,hmin⟩ := hSnonempty.isLeast_csInf hSfinite
  have hτpos : 0 < τ.val := hτ.1
  let R : CurveComplex.Interval → CurveComplex.Interval := fun t =>
    ⟨τ.val*t.val,by
      constructor
      · exact mul_nonneg hτpos.le t.property.1
      · nlinarith [τ.property.2,t.property.2,t.property.1]⟩
  have hRcont : Continuous R := by fun_prop
  have hRinj : Function.Injective R := by
    intro t s h
    apply Subtype.ext
    have hh := congrArg Subtype.val h
    change τ.val*t.val=τ.val*s.val at hh
    exact mul_left_cancel₀ hτpos.ne' hh
  let p : Path u (f τ) := {
    toFun := f ∘ R
    continuous_toFun := f.continuous.comp hRcont
    source' := by simpa [R] using f.source
    target' := by simp [R] }
  have hp : IsEmbedding p := (p.continuous.isClosedEmbedding (hf.injective.comp hRinj)).isEmbedding
  refine ⟨f τ,?_,p,hp,?_,?_,hτ.2⟩
  · intro h
    have hh : f 0=f τ := f.source.trans h
    have ht := hf.injective hh
    exact (ne_of_gt hτ.1) ht.symm
  · rintro x ⟨t,rfl⟩
    exact hA (Set.mem_range_self (R t))
  · rintro x ⟨t,ht,rfl⟩ hx
    have hrpos : 0 < R t := by change 0 < τ.val*t.val; exact mul_pos hτpos ht.1
    have hrlt : R t < τ := by change τ.val*t.val < τ.val; exact (mul_lt_mul_of_pos_left (show t.val < 1 from ht.2) hτpos).trans_eq (mul_one _)
    have hmem : R t ∈ S := ⟨hrpos,hx⟩
    exact (not_le_of_gt hrlt) (hmin hmem)

private theorem curve_embedded_path_between
    {X : Type} [TopologicalSpace X] [T2Space X]
    (a : Curve X) {u z : X} (hu : u ∈ a.image) (hz : z ∈ a.image) (huz : u ≠ z) :
    ∃ f : Path u z, IsEmbedding f ∧ Set.range f ⊆ a.image := by
  obtain ⟨x,hx⟩ := hu
  obtain ⟨y,hy⟩ := hz
  have hxy : x ≠ y := by intro h; apply huz; rw [←hx,←hy,h]
  let f : Path u z := ((Circle.path x y).map a.embedded.continuous).cast hx.symm hy.symm
  have hf : Function.Injective f := a.embedded.injective.comp (Circle.path_injective_of_ne hxy)
  refine ⟨f,(f.continuous.isClosedEmbedding hf).isEmbedding,?_⟩
  rintro w ⟨t,rfl⟩
  exact Set.mem_range_self _

private theorem finite_two_crossing_clean_paths
    {X : Type} [TopologicalSpace X] [T2Space X]
    (a b : Curve X) (hfinite : (a.image ∩ b.image).Finite)
    (hcount : 2 ≤ (a.image ∩ b.image).ncard) :
    ∃ u z : X, u ≠ z ∧ ∃ f g : Path u z,
      IsEmbedding f ∧ IsEmbedding g ∧ Set.range f ⊆ a.image ∧
      Set.range g ⊆ b.image ∧ f '' Set.Ioo (0 : CurveComplex.Interval) 1 ⊆ b.imageᶜ := by
  obtain ⟨u,hu,v,hv,huv⟩ := (Set.one_lt_ncard hfinite).mp (by omega)
  obtain ⟨f,hf,hfa⟩ := curve_embedded_path_between a hu.1 hv.1 huv
  obtain ⟨z,huz,p,hp,hpa,hclean,hzb⟩ := first_contact_embedded_path f hf
    a.image b.image hfa hfinite hv.2
  obtain ⟨g,hg,hgb⟩ := curve_embedded_path_between b hu.2 hzb huz
  exact ⟨u,z,huz,p,g,hp,hg,hpa,hgb,hclean⟩

private theorem common_lift_endpoints_homotopic
    {P X : Type} [TopologicalSpace P] [SimplyConnectedSpace P]
    [TopologicalSpace X] (q : C(P,X)) {x y : P} (f g : Path x y) :
    (f.map q.continuous).Homotopic (g.map q.continuous) := by
  exact (SimplyConnectedSpace.paths_homotopic f g).map q

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Topology Set
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

/-- Source-only geometric selection. Outputs actual embedded paths with the
SAME source endpoints and fixed-endpoint homotopy, never a disk or isotope. -/
theorem actual_free_homotopy_two_crossing_clean_matched_paths
    (H : ClosedHyperbolicMetric E) (a b : Curve E)
    (ha : Essential a) (hb : Essential b)
    (hhom : FreeHomotopic ⟨a.map,a.embedded.continuous⟩
      ⟨b.map,b.embedded.continuous⟩)
    (ht : Transverse a b) (hcount : 2 ≤ (a.image ∩ b.image).ncard) :
    ∃ u z : E, u ≠ z ∧ ∃ f g : Path u z,
      IsEmbedding f ∧ IsEmbedding g ∧
      Set.range f ⊆ a.image ∧ Set.range g ⊆ b.image ∧
      f '' Set.Ioo (0 : Interval) 1 ⊆ b.imageᶜ ∧ f.Homotopic g := by
  classical
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    letI : MetricSpace E := H.metric
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  have actual_free_homotopy_strip_lift
      {P X G : Type} [TopologicalSpace P] [TopologicalSpace X]
      [Group G] [MulAction G P]
      (p : P → X) (hp : IsQuotientCoveringMap p G)
      (F : C(Circle × Interval,X)) (x₀ : P)
      (hx₀ : p x₀ = F (1,0)) :
      ∃ L : C(ℝ × Interval,P), ∃ g : G,
        L (0,0) = x₀ ∧
        (∀ (s : ℝ) (t : Interval), p (L (s,t)) = F (Circle.exp s,t)) ∧
        (∀ (s : ℝ) (t : Interval), L (s+2*Real.pi,t) = g • L (s,t)) := by
    classical
    letI : ContinuousConstSMul G P := hp.toContinuousConstSMul
    letI : ContractibleSpace Interval := (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).contractibleSpace
      (show (Set.Icc (0:ℝ) 1).Nonempty from ⟨0,by norm_num⟩)
    letI : LocallyPathConnectedSpace Interval :=
      (convex_Icc (0:ℝ) 1 : Convex ℝ (Set.Icc (0:ℝ) 1)).locallyPathConnectedSpace
    let strip : C(ℝ × Interval,X) :=
      ⟨fun st => F (Circle.exp st.1,st.2),
        F.continuous.comp ((Circle.exp.continuous.comp continuous_fst).prodMk continuous_snd)⟩
    have hxstrip : p x₀ = strip (0,0) := by simpa [strip] using hx₀
    obtain ⟨L,⟨hL₀,hLift⟩,hUnique⟩ :=
      hp.isCoveringMap.existsUnique_continuousMap_lifts strip (0,0) x₀ hxstrip
    have hproject (s : ℝ) (t : Interval) : p (L (s,t)) = F (Circle.exp s,t) :=
      congrFun hLift (s,t)
    have hsame : p (L (2*Real.pi,0)) = p (L (0,0)) := by
      rw [hproject,hproject,Circle.exp_two_pi,Circle.exp_zero]
    obtain ⟨g,hg⟩ := hp.apply_eq_iff_mem_orbit.mp hsame
    let M : C(ℝ × Interval,P) :=
      ⟨fun st => g⁻¹ • L (st.1+2*Real.pi,st.2),by fun_prop⟩
    have hM₀ : M (0,0) = x₀ := by
      change g⁻¹ • L (0+2*Real.pi,0) = x₀
      rw [zero_add,← hg,inv_smul_smul,hL₀]
    have hMproject : p ∘ M = strip := by
      funext st
      change p (g⁻¹ • L (st.1+2*Real.pi,st.2)) = F (Circle.exp st.1,st.2)
      rw [hp.map_smul,hproject,Circle.exp_add_two_pi]
    have hML : M = L := hUnique M ⟨hM₀,hMproject⟩
    refine ⟨L,g,hL₀,hproject,?_⟩
    intro s t
    have h := congrArg (fun N : C(ℝ × Interval,P) => g • N (s,t)) hML
    change g • (g⁻¹ • L (s+2*Real.pi,t)) = g • L (s,t) at h
    simpa only [smul_inv_smul] using h
  have actual_source_homotopy_component_strip
      {P G : Type} [TopologicalSpace P] [Group G] [MulAction G P]
      (p : P → connectedComponent (a.map 1)) (hp : IsQuotientCoveringMap p G) :
      ∃ L : C(ℝ × Interval,P), ∃ g : G,
        (∀ (s : ℝ), (p (L (s,0))).val = a.map (Circle.exp s)) ∧
        (∀ (s : ℝ), (p (L (s,1))).val = b.map (Circle.exp s)) ∧
        (∀ (s : ℝ) (t : Interval), L (s+2*Real.pi,t) = g • L (s,t)) := by
    classical
    obtain ⟨F,hF₀,hF₁⟩ := hhom
    have hFrange : Set.range F ⊆ connectedComponent (a.map 1) := by
      apply (isConnected_range F.continuous).subset_connectedComponent
      exact ⟨(1,0),hF₀ 1⟩
    let componentF : C(Circle × Interval,connectedComponent (a.map 1)) :=
      ⟨fun z => ⟨F z,hFrange (Set.mem_range_self z)⟩,F.continuous.subtype_mk _⟩
    let base : connectedComponent (a.map 1) := ⟨a.map 1,mem_connectedComponent⟩
    obtain ⟨x₀,hx₀⟩ := hp.surjective base
    have hxF : p x₀ = componentF (1,0) := by
      rw [hx₀]
      apply Subtype.ext
      exact (hF₀ 1).symm
    obtain ⟨L,g,hL₀,hLproj,hLperiod⟩ := actual_free_homotopy_strip_lift p hp componentF x₀ hxF
    refine ⟨L,g,?_,?_,hLperiod⟩
    · intro s
      exact (congrArg Subtype.val (hLproj s 0)).trans (hF₀ (Circle.exp s))
    · intro s
      exact (congrArg Subtype.val (hLproj s 1)).trans (hF₁ (Circle.exp s))
  letI : CompactSpace E := H.compact
  let A := connectedComponent (a.map 1)
  letI : CompactSpace A := isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  letI : ConnectedSpace A := isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  letI : LocallyConnectedSpace E := ChartedSpace.locallyConnectedSpace
    (EuclideanSpace ℝ (Fin 2)) E
  have haOpen : IsOpen A := isOpen_connectedComponent
  let componentOpen : TopologicalSpace.Opens E := ⟨A,haOpen⟩
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) A :=
    TopologicalSpace.Opens.instChartedSpace componentOpen
  let base : A := ⟨a.map 1,mem_connectedComponent⟩
  obtain ⟨coverTopology,hsecond,hcoverT2,hcharts,hsc,hqc,hsurj,hlift⟩ :=
    actual_topological_universal_cover base
  let P := Σ z : A, Path.Homotopic.Quotient base z
  letI : TopologicalSpace P := coverTopology
  letI : SecondCountableTopology P := hsecond
  letI : T2Space P := hcoverT2
  letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) P := hcharts.some
  letI : SimplyConnectedSpace P := hsc
  obtain ⟨development,development_metric⟩ :=
    actual_hyperbolic_component_simply_connected_cover_develops H (a.map 1)
      (Sigma.fst : P → A) hqc.isCoveringMap hsurj
  obtain ⟨L,monodromy,hL0,hL1,hLperiod⟩ :=
    actual_source_homotopy_component_strip (Sigma.fst : P → A) hqc
  let sourceLift : C(ℝ,H2) := ⟨fun s => development (L (s,0)),
    development.continuous.comp (L.continuous.comp
      (continuous_id.prodMk continuous_const))⟩
  let targetLift : C(ℝ,H2) := ⟨fun s => development (L (s,1)),
    development.continuous.comp (L.continuous.comp
      (continuous_id.prodMk continuous_const))⟩
  let developedProjection : H2 → E := fun z => (development.symm z).1.val
  have sourceLift_projection (s : ℝ) :
      developedProjection (sourceLift s) = a.map (Circle.exp s) := by
    change (development.symm (development (L (s,0)))).1.val = _
    rw [development.symm_apply_apply]
    exact hL0 s
  have targetLift_projection (s : ℝ) :
      developedProjection (targetLift s) = b.map (Circle.exp s) := by
    change (development.symm (development (L (s,1)))).1.val = _
    rw [development.symm_apply_apply]
    exact hL1 s
  let developedDeck : deck (Sigma.fst : P → A) → H2 ≃ₜ H2 :=
    fun k => (development.symm.trans k.val).trans development
  have developedDeck_projection (k : deck (Sigma.fst : P → A)) (z : H2) :
      developedProjection (developedDeck k z) = developedProjection z := by
    change (development.symm (development (k • development.symm z))).1.val = _
    rw [development.symm_apply_apply]
    exact congrArg Subtype.val (hqc.map_smul k)
  have sourceLift_period (s : ℝ) : sourceLift (s+2*Real.pi) =
      developedDeck monodromy (sourceLift s) := by
    change development (L (s+2*Real.pi,0)) =
      development (monodromy • development.symm (development (L (s,0))))
    rw [hLperiod,development.symm_apply_apply]
  have targetLift_period (s : ℝ) : targetLift (s+2*Real.pi) =
      developedDeck monodromy (targetLift s) := by
    change development (L (s+2*Real.pi,1)) =
      development (monodromy • development.symm (development (L (s,1))))
    rw [hLperiod,development.symm_apply_apply]
  have monodromy_ne_one : monodromy ≠ 1 := by
    intro hm
    letI : Fact (0 < 2*Real.pi) := ⟨by positivity⟩
    let bottom : C(ℝ,P) := ⟨fun s => L (s,0),
      L.continuous.comp (continuous_id.prodMk continuous_const)⟩
    have hend : bottom 0 = bottom (2*Real.pi) := by
      have hh := hLperiod 0 0
      simpa [bottom,hm] using hh.symm
    let circleLift : C(Circle,P) :=
      ⟨fun z => AddCircle.liftIco (2*Real.pi) 0 bottom (AddCircle.homeomorphCircle'.symm z),
        (AddCircle.liftIco_zero_continuous hend bottom.continuous.continuousOn).comp
          AddCircle.homeomorphCircle'.symm.continuous⟩
    have hcircle (z : Circle) : (circleLift z).1.val = a.map z := by
      change (L (((AddCircle.equivIco (2*Real.pi) 0)
        (AddCircle.homeomorphCircle'.symm z)),0)).1.val = _
      rw [hL0]
      rw [← AddCircle.homeomorphCircle'_apply_mk, AddCircle.coe_equivIco,
        AddCircle.homeomorphCircle'.apply_symm_apply]
    obtain ⟨plane⟩ := actual_hyperbolic_component_simply_connected_cover_is_plane
      H (a.map 1) (Sigma.fst : P → A) hqc.isCoveringMap hsurj
    have hprojection : Continuous (fun z : P => z.1.val) :=
      continuous_subtype_val.comp hqc.isCoveringMap.continuous
    let contraction : C(Circle × Interval,E) :=
      ⟨fun zt => (plane ((1 - zt.2.val) • plane.symm (circleLift zt.1))).1.val,
        hprojection.comp (plane.continuous.comp
          ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).smul
            (plane.symm.continuous.comp (circleLift.continuous.comp continuous_fst))))⟩
    apply essential_curve_is_essential_loop H a ha
    refine ⟨(plane 0).1.val,contraction,?_,?_⟩
    · intro z
      change (plane ((1 - (0 : ℝ)) • plane.symm (circleLift z))).1.val = a.map z
      simpa using hcircle z
    · intro z
      change (plane ((1 - (1 : ℝ)) • plane.symm (circleLift z))).1.val = (plane 0).1.val
      simp
  have monodromy_no_fixed_point (x : P) : monodromy • x ≠ x := by
    intro hx
    letI : IsCancelSMul (deck (Sigma.fst : P → A)) P := hqc.isCancelSMul
    exact monodromy_ne_one (IsCancelSMul.right_cancel _ _ x (by simpa using hx))
  let sourceComponentMetric : MetricSpace A := MetricSpace.induced Subtype.val Subtype.val_injective H.metric
  have sourceComponentMetric_topology :
      sourceComponentMetric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace A) := by
    change TopologicalSpace.induced Subtype.val
      H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
      TopologicalSpace.induced Subtype.val (inferInstance : TopologicalSpace E)
    rw [H.compatible]
  letI : MetricSpace A := sourceComponentMetric.replaceTopology sourceComponentMetric_topology.symm
  have actual_segment := actual_metric_path_segment
  have all_developed_decks_isometric (k : deck (Sigma.fst : P → A)) : Isometry (developedDeck k) := by
    apply actual_deck_development_isometry (Sigma.fst : P → A) development
    · intro x
      obtain ⟨U,hU,hx,hmetric⟩ := development_metric x
      exact ⟨U,hU,hx,hmetric⟩
    · intro x
      exact hqc.map_smul k
  have fiber_nonempty (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := by
    obtain ⟨z,hz⟩ := hsurj a
    exact ⟨⟨z,hz⟩⟩
  letI (a : A) : Nonempty ((Sigma.fst : P → A) ⁻¹' {a}) := fiber_nonempty a
  have actualCoveringMap : IsCoveringMap (Sigma.fst : P → A) := hqc.isCoveringMap
  let actualTrivialization (a : A) := (actualCoveringMap a).toTrivialization
  have actualTrivialization_base (a : A) : a ∈ (actualTrivialization a).baseSet :=
    (actualCoveringMap a).mem_toTrivialization_baseSet
  have uniform_evenly_covered_radius : ∃ ε : ℝ, 0 < ε ∧ ∀ x : A,
      ∃ a : A, Metric.ball x ε ⊆ (actualTrivialization a).baseSet := by
    obtain ⟨ε,hε,hcover⟩ := lebesgue_number_lemma_of_metric isCompact_univ
      (fun a => (actualTrivialization a).open_baseSet)
      (show Set.univ ⊆ ⋃ a, (actualTrivialization a).baseSet from
        fun x _ => Set.mem_iUnion.mpr ⟨x,actualTrivialization_base x⟩)
    exact ⟨ε,hε,fun x => hcover x (Set.mem_univ x)⟩
  let componentProjection : H2 → A := fun z => (development.symm z).1
  have componentProjection_continuous : Continuous componentProjection :=
    actualCoveringMap.continuous.comp development.symm.continuous
  have componentProjection_locally_isometric (x : H2) :
      ∃ U : Set H2, IsOpen U ∧ x ∈ U ∧
        ∀ y ∈ U, ∀ z ∈ U,
          dist (componentProjection y) (componentProjection z) = dist y z := by
    obtain ⟨U,hU,hxU,hmetric⟩ := development_metric (development.symm x)
    refine ⟨development.symm ⁻¹' U,hU.preimage development.symm.continuous,hxU,?_⟩
    intro y hy z hz
    change @dist E H.metric.toDist (development.symm y).1.val
      (development.symm z).1.val = dist y z
    rw [hmetric _ hy _ hz,development.apply_symm_apply,development.apply_symm_apply]
  have componentProjection_nonexpanding (x y : H2) :
      dist (componentProjection x) (componentProjection y) ≤ dist x y := by
    obtain ⟨γ,hγ⟩ := actual_segment x y
    choose U hU hxU hmetric using componentProjection_locally_isometric
    let V : Interval → Set Interval := fun t => γ ⁻¹' U (γ t)
    have hV (t : Interval) : IsOpen (V t) := (hU (γ t)).preimage γ.continuous
    have hcover : Set.univ ⊆ ⋃ t, V t := by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,hxU (γ t)⟩
    obtain ⟨t,ht0,htmono,⟨N,hN⟩,hsub⟩ :=
      exists_monotone_Icc_subset_open_cover_unitInterval hV hcover
    have hstep (n : ℕ) :
        dist (componentProjection (γ (t n))) (componentProjection (γ (t (n+1)))) =
          dist x y * ((t (n+1) : ℝ) - (t n : ℝ)) := by
      obtain ⟨j,hj⟩ := hsub n
      have hle : t n ≤ t (n+1) := htmono (Nat.le_succ n)
      have hleft := hj (show t n ∈ Set.Icc (t n) (t (n+1)) from ⟨le_rfl,hle⟩)
      have hright := hj (show t (n+1) ∈ Set.Icc (t n) (t (n+1)) from ⟨hle,le_rfl⟩)
      rw [hmetric (γ j) _ hleft _ hright,hγ,Real.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (t n : ℝ) ≤ (t (n+1) : ℝ) from hle))]
      simp only [neg_sub]
    have hbound (n : ℕ) :
        dist (componentProjection (γ (t 0))) (componentProjection (γ (t n))) ≤
          dist x y * ((t n : ℝ) - (t 0 : ℝ)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have htri := dist_triangle (componentProjection (γ (t 0)))
          (componentProjection (γ (t n))) (componentProjection (γ (t (n+1))))
        have hsn := hstep n
        nlinarith
    have h := hbound N
    rw [ht0,hN N le_rfl] at h
    simpa using h
  have developed_monodromy_no_fixed_point (z : H2) :
      developedDeck monodromy z ≠ z := by
    intro hz
    apply monodromy_no_fixed_point (development.symm z)
    apply development.injective
    change development (monodromy • development.symm z) = development (development.symm z)
    simpa only [developedDeck,Homeomorph.trans_apply,Homeomorph.symm_apply_apply,
      development.apply_symm_apply,Subgroup.smul_def,Homeomorph.smul_def] using hz
  obtain ⟨coverRadius,coverRadius_pos,coverRadius_control⟩ := uniform_evenly_covered_radius
  have actual_positive_uniform_deck_displacement (z : H2) :
      coverRadius ≤ dist z ((developedDeck monodromy) z) := by
    by_contra hle
    have hshort : dist z ((developedDeck monodromy) z) < coverRadius := lt_of_not_ge hle
    obtain ⟨a,ha⟩ := coverRadius_control (componentProjection z)
    obtain ⟨γ,hγ⟩ := actual_segment z ((developedDeck monodromy) z)
    let Γ : C(Interval,P) := ⟨development.symm ∘ γ,
      development.symm.continuous.comp γ.continuous⟩
    let T := actualTrivialization a
    letI : DiscreteTopology ((Sigma.fst : P → A) ⁻¹' {a}) :=
      (actualCoveringMap a).discreteTopology_fiber
    have hsource (t : Interval) : Γ t ∈ T.source := by
      apply T.mem_source.mpr
      apply ha
      change dist (componentProjection (γ t)) (componentProjection z) < coverRadius
      have hπ := componentProjection_nonexpanding (γ t) z
      have hseg : dist (γ t) z = dist z ((developedDeck monodromy) z) * (t : ℝ) := by
        have h := hγ 0 t
        simpa [Real.dist_eq,abs_of_nonneg t.property.1,dist_comm] using h
      have hbound := mul_le_of_le_one_right
        (dist_nonneg (x := z) (y := (developedDeck monodromy) z)) t.property.2
      rw [hseg] at hπ
      exact lt_of_le_of_lt (hπ.trans hbound) hshort
    let label : Interval → ((Sigma.fst : P → A) ⁻¹' {a}) := fun t => (T (Γ t)).2
    have hlabel : Continuous label := continuous_snd.comp
      (T.toOpenPartialHomeomorph.continuousOn.comp_continuous Γ.continuous hsource)
    have hlabels : label 0 = label 1 :=
      (isPreconnected_range hlabel).subsingleton (mem_range_self 0) (mem_range_self 1)
    have hprojection : (Γ 0).1 = (Γ 1).1 := by
      change (development.symm (γ 0)).1 = (development.symm (γ 1)).1
      rw [γ.source,γ.target]
      change (development.symm z).1 =
        (development.symm (development (monodromy • development.symm z))).1
      rw [development.symm_apply_apply]
      exact (hqc.map_smul monodromy).symm
    have hcoords : T (Γ 0) = T (Γ 1) := by
      apply Prod.ext
      · change (T.toOpenPartialHomeomorph (Γ 0)).1 =
          (T.toOpenPartialHomeomorph (Γ 1)).1
        rw [T.proj_toFun _ (hsource 0),T.proj_toFun _ (hsource 1)]
        exact hprojection
      · exact hlabels
    have hend : Γ 0 = Γ 1 := T.injOn (hsource 0) (hsource 1) hcoords
    apply developed_monodromy_no_fixed_point z
    have h := congrArg development hend
    change development (development.symm (γ 0)) = development (development.symm (γ 1)) at h
    simpa only [development.apply_symm_apply,γ.source,γ.target] using h.symm
  letI : MulAction (deck (Sigma.fst : P → A)) H2 := actual_conjugated_cover_action development.symm
  have hqcdev : IsQuotientCoveringMap componentProjection (deck (Sigma.fst : P → A)) :=
    actual_cover_with_conjugated_action (Sigma.fst : P → A) hqc development.symm
  have hdeckdev (k : deck (Sigma.fst : P → A)) : Isometry (fun z : H2 => k • z) :=
    all_developed_decks_isometric k
  have haA (z : Circle) : a.map z ∈ A := by
    obtain ⟨u,rfl⟩ := Circle.exp_surjective z
    rw [←hL0]
    exact (L (u,0)).1.property
  have hbA (z : Circle) : b.map z ∈ A := by
    obtain ⟨u,rfl⟩ := Circle.exp_surjective z
    rw [←hL1]
    exact (L (u,1)).1.property
  let a' : Curve A := {
    map := fun z => ⟨a.map z,haA z⟩
    embedded := (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp a.embedded }
  let b' : Curve A := {
    map := fun z => ⟨b.map z,hbA z⟩
    embedded := (Topology.IsEmbedding.of_comp_iff Topology.IsEmbedding.subtypeVal).mp b.embedded }
  have ha' (z : Circle) : (a'.map z).val=a.map z := rfl
  have hb' (z : Circle) : (b'.map z).val=b.map z := rfl
  obtain ⟨ht',hcount'⟩ := actual_open_subtype_curves_retain_transverse_count A haOpen a b a' b'
    ha' hb' ht hcount
  have hF' (u : ℝ) : componentProjection (sourceLift u)=a'.map (Circle.exp u) := by
    apply Subtype.ext
    exact sourceLift_projection u
  have hJ' (u : ℝ) : componentProjection (targetLift u)=b'.map (Circle.exp u) := by
    apply Subtype.ext
    exact targetLift_projection u
  obtain ⟨u,z,huz,f,j,hf,hj,hfa,hjb,hclean,hhompaths⟩ :=
    periodic_original_lifts_produce_actual_clean_matched_paths componentProjection hqcdev hdeckdev
      a' b' ht' hcount' sourceLift targetLift monodromy coverRadius coverRadius_pos
      actual_positive_uniform_deck_displacement hF' hJ' sourceLift_period targetLift_period
  let fp : Path u.val z.val := f.map continuous_subtype_val
  let jp : Path u.val z.val := j.map continuous_subtype_val
  refine ⟨u.val,z.val,fun he => huz (Subtype.ext he),fp,jp,
    Topology.IsEmbedding.subtypeVal.comp hf,Topology.IsEmbedding.subtypeVal.comp hj,?_,?_,?_,?_⟩
  · rintro w ⟨v,rfl⟩
    obtain ⟨x,hx⟩ := hfa (Set.mem_range_self v)
    exact ⟨x,(ha' x).symm.trans (congrArg Subtype.val hx)⟩
  · rintro w ⟨v,rfl⟩
    obtain ⟨x,hx⟩ := hjb (Set.mem_range_self v)
    exact ⟨x,(hb' x).symm.trans (congrArg Subtype.val hx)⟩
  · rintro w ⟨v,hv,rfl⟩ hw
    obtain ⟨x,hx⟩ := hw
    apply hclean ⟨v,hv,rfl⟩
    exact ⟨x,Subtype.ext ((hb' x).trans hx)⟩
  · exact hhompaths.map ⟨Subtype.val,continuous_subtype_val⟩

end CurveComplex.Hyperbolic
