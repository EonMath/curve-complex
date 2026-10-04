import CurveComplexGenusTwo.Topology.WeightedSurgery.ArcSurgeryProducers
import CurveComplexGenusTwo.Topology.Smoothing.ActualSmoothChartStar
import CurveComplexGenusTwo.Topology.Smoothing.ActualStarIntersection
import CurveComplexGenusTwo.Topology.Smoothing.PrescribedPairRadializationProof
import CurveComplexGenusTwo.Topology.Smoothing.FiniteActualStarRadialization
import CurveComplexGenusTwo.Topology.Smoothing.ActualGermArcs
import CurveComplexGenusTwo.Topology.WeightedSurgery.SupportedEndpointRotation
import Schoenflies.PolyLocal
namespace CurveComplex.HyperellipticModel
open Set Metric Topology Schoenflies CurveComplex.FiniteStarGeometry
open ArcSurgery
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 2000000
private theorem endpoint_germs_from_finite_contacts
    (M : HyperellipticModel E S) {ι : Type} [Fintype ι]
    (old : ι → EssentialMarkedArc M)
    (hfinite : ∀ i j, i ≠ j → (crossings M (old i) (old j)).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
    (∀ v : ι × Bool,
      (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p →
      ∀ t, (old v.1).val.map (endpointGermParameter v.2 r hr (by linarith) t) ∈ W) ∧
    ∀ v w : ι × Bool, v ≠ w →
      (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p →
      (if w.2 then (old w.1).val.map 1 else (old w.1).val.map 0)=p →
      Set.range ((old v.1).val.map ∘ endpointGermParameter v.2 r hr (by linarith)) ∩
        Set.range ((old w.1).val.map ∘ endpointGermParameter w.2 r hr (by linarith)) = {p} := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let contacts : Set S := ⋃ i, ⋃ j, if i=j then ∅ else crossings M (old i) (old j)
  have hc : contacts.Finite := by
    apply Set.finite_iUnion
    intro i
    apply Set.finite_iUnion
    intro j
    split
    · exact Set.finite_empty
    · exact hfinite i j ‹i ≠ j›
  have hpc : p ∉ contacts := by
    intro h
    obtain ⟨i,j,h⟩ := Set.mem_iUnion₂.mp h
    split at h
    · exact Set.notMem_empty p h
    · exact h.1.2 hp
  obtain ⟨r,hr,hrhalf,hstarts,hends⟩ :=
    uniform_actual_endpoint_germs M ι old p (contactsᶜ ∩ W)
      (hc.isClosed.isOpen_compl.inter hW) ⟨hpc,hpW⟩
  have hr1 : r < 1 := by linarith
  let germ (v : ι × Bool) := (old v.1).val.map ∘ endpointGermParameter v.2 r hr hr1
  have hzero (v : ι × Bool)
      (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p) :
      germ v 0=p := by
    cases hb : v.2 <;> simpa [germ,endpointGermParameter,hb] using hv
  have hlocal (v : ι × Bool)
      (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p)
      (t : Interval) : germ v t ∈ contactsᶜ ∩ W := by
    cases hb : v.2
    · apply hstarts v.1 (by simpa [hb] using hv)
      rw [hb]
      change r*t.val ≤ r
      nlinarith [t.property.2]
    · apply hends v.1 (by simpa [hb] using hv)
      rw [hb]
      change 1-r ≤ 1-r*t.val
      nlinarith [t.property.2]
  have hoff (v : ι × Bool)
      (hv : (if v.2 then (old v.1).val.map 1 else (old v.1).val.map 0)=p)
      (t : Interval) : germ v t ∉ contacts := (hlocal v hv t).1
  have hmarked (v : ι × Bool) (t : Interval)
      (hm : germ v t ∈ M.cover.branch) : t=0 := by
    obtain ht | ht := (old v.1).val.marked_only_at_ends
      (endpointGermParameter v.2 r hr hr1 t) hm
    · have hh := congrArg Subtype.val ht
      apply Subtype.ext
      change t.val=0
      cases hb : v.2 <;> simp [endpointGermParameter,hb,ne_of_gt hr] at hh <;>
        first | exact congrArg Subtype.val hh | nlinarith [t.property.1,t.property.2]
    · have hh := congrArg Subtype.val ht
      apply Subtype.ext
      change t.val=0
      cases hb : v.2 <;> simp [endpointGermParameter,hb,ne_of_gt hr] at hh <;>
        first | exact congrArg Subtype.val hh | nlinarith [t.property.1,t.property.2]
  refine ⟨r,hr,hrhalf,(fun v hv t => (hlocal v hv t).2),?_⟩
  intro v w hvw hv hw
  by_cases he : v.1=w.1
  · have hb : v.2 ≠ w.2 := fun hh => hvw (Prod.ext he hh)
    let solo : Unit → EssentialMarkedArc M := fun _ => old v.1
    have hdsolo : ∀ i j : Unit, i ≠ j → Disjoint (arcInterior M (solo i)) (arcInterior M (solo j)) := by
      intro i j hij
      exact (hij (Subsingleton.elim _ _)).elim
    have hs := actual_normalized_star_intersection M solo hdsolo p r hr hrhalf
      ((),v.2) ((),w.2) (fun hh => hb (congrArg (fun z : Unit × Bool => z.2) hh))
      (by simpa [solo,germ,endpointGermParameter] using hzero v hv)
      (by simpa [solo,germ,endpointGermParameter,he] using hzero w hw)
    simpa only [solo,he] using hs
  · ext x
    constructor
    · rintro ⟨⟨t,ht⟩,⟨u,hu⟩⟩
      have heq : germ v t = germ w u := ht.trans hu.symm
      by_cases hm : germ v t ∈ M.cover.branch
      · change germ v t=x at ht
        rw [hmarked v t hm,hzero v hv] at ht
        exact Set.mem_singleton_iff.mpr ht.symm
      · have hcontact : germ v t ∈ crossings M (old v.1) (old w.1) := by
          refine ⟨⟨?_,hm⟩,?_,hm⟩
          · exact ⟨endpointGermParameter v.2 r hr hr1 t,rfl⟩
          · exact ⟨endpointGermParameter w.2 r hr hr1 u,heq.symm⟩
        exact False.elim (hoff v hv t (Set.mem_iUnion₂.mpr ⟨v.1,w.1,by simpa [he] using hcontact⟩))
    · intro hx
      have hx' := Set.mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨0,hzero v hv⟩,⟨0,hzero w hw⟩⟩
private theorem radialized_prefix_common_cut (γ : I → Plane) (hγ : Topology.IsClosedEmbedding γ)
    (o : Plane) (hstart : γ zeroI = o) (H : Plane ≃ₜ Plane) (hH : H o = o)
    (c d : I) (hd : 0 < d.val) (hdc : d.val ≤ c.val) (v : Plane) (hv : v ≠ 0)
    (hrad : H '' armPrefix (fun _ : Unit => γ) () c = segment ℝ o (o+v)) :
    H '' armPrefix (fun _ : Unit => γ) () d = segment ℝ o (H (γ d)) ∧ H (γ d) ≠ o := by
  let k : I → I := fun t => ⟨d.val*t.val,by
    constructor
    · exact mul_nonneg d.property.1 t.property.1
    · nlinarith [d.property.1,d.property.2,t.property.1,t.property.2]⟩
  let η : Path o (H (γ d)) := {
    toFun := H ∘ γ ∘ k
    continuous_toFun := H.continuous.comp (hγ.continuous.comp (by fun_prop))
    source' := by simpa [k] using (congrArg H hstart).trans hH
    target' := by simp [k] }
  have hη : Function.Injective η := by
    intro t u he
    have hh := congrArg Subtype.val (hγ.injective (H.injective he))
    change d.val*t.val = d.val*u.val at hh
    exact Subtype.ext (mul_left_cancel₀ (ne_of_gt hd) hh)
  have himage : range η = H '' armPrefix (fun _ : Unit => γ) () d := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨γ (k t),⟨k t,by change d.val*t.val ≤ d.val; nlinarith [d.property.1,t.property.2],rfl⟩,rfl⟩
    · rintro ⟨_,⟨t,ht,rfl⟩,rfl⟩
      let u : I := ⟨t.val/d.val,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
      refine ⟨u,?_⟩
      change H (γ (k u)) = H (γ t)
      congr 2
      apply Subtype.ext
      change d.val*(t.val/d.val) = t.val
      field_simp
  have hA : IsArcBetween (range η) o (H (γ d)) := by
    refine ⟨η.extend,η.continuous_extend.continuousOn,?_,?_,η.extend_zero,η.extend_one⟩
    · intro s hs t ht he
      rw [Path.extend_apply _ hs,Path.extend_apply _ ht] at he
      exact congrArg Subtype.val (hη he)
    · exact η.image_extend_of_subset (Subset.refl (Icc (0:ℝ) 1))
  have hneq : H (γ d) ≠ o := by
    intro he
    have hdz : d = zeroI := hγ.injective ((H.injective (he.trans hH.symm)).trans hstart.symm)
    have hh : d.val = 0 := congrArg Subtype.val hdz
    linarith
  have hvend : o ≠ o+v := by
    intro he
    apply hv
    have hh := congrArg (fun x => x-o) he
    simpa only [sub_self,add_sub_cancel_left] using hh.symm
  have hC := isArcBetween_segment hvend
  have hAC : range η ⊆ segment ℝ o (o+v) := by
    rw [himage,← hrad]
    apply image_mono
    apply image_mono
    intro t ht
    exact ht.trans hdc
  have hqC : H (γ d) ∈ segment ℝ o (o+v) := by
    rw [← hrad]
    exact ⟨γ d,⟨d,hdc,rfl⟩,rfl⟩
  have hBC : segment ℝ o (H (γ d)) ⊆ segment ℝ o (o+v) :=
    (convex_segment o (o+v)).segment_subset (left_mem_segment ℝ o (o+v)) hqC
  exact ⟨himage.symm.trans (hA.eq_of_subset_arc (isArcBetween_segment hneq.symm) hC hAC hBC),hneq⟩

theorem marked_endpoint_source_fan_unnormalized
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (a : J → EssentialMarkedArc M)
    (hfinite : ∀ i j, i ≠ j → (ArcSurgery.crossings M (a i) (a j)).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (g₀ : J × Bool)
    (hg₀ : (if g₀.2 then (a g₀.1).val.map 1 else (a g₀.1).val.map 0) = p) :
    let incident : J × Bool → Prop := fun g =>
      (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S) = {p} ∧
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
    ∃ v : J × Bool → Plane,
      (∀ g, incident g → v g ≠ 0) ∧
      (incident (g₀.1,!g₀.2) → ∃ ell : ℝ, 0 < ell ∧ v (g₀.1,!g₀.2) = -ell • v g₀) ∧
      (∀ g k, incident g → incident k → g ≠ k →
        segment ℝ (0 : Plane) (v g) ∩ segment ℝ (0 : Plane) (v k) = {0}) ∧
      (∀ g, incident g →
        Set.range ((a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
        Set.range (F ∘ (a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
          segment ℝ (0 : Plane) (v g)) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let C := actualSphereSmoothAtlas M
  letI := C.charts
  obtain ⟨U,hU,hpU,hUchart,hmarks,hcentral,hnoninc,rOld,hrOld,hrOldHalf,hOldGerms⟩ :=
    actual_endpoint_star_in_smooth_chart M C J a p hp
  let D := U ∩ W
  have hD : IsOpen D := hU.inter hW
  have hpD : p ∈ D := ⟨hpU,hpW⟩
  let e0 := chartAt Plane p
  let e : OpenPartialHomeomorph S Plane :=
    (e0.restr D).trans (Homeomorph.addRight (-e0 p)).toOpenPartialHomeomorph
  have heSource : e.source = e0.source ∩ D := by simp [e,hD.interior_eq]
  have hep : p ∈ e.source := heSource.symm ▸ ⟨mem_chart_source _ _,hpD⟩
  have heval (x : S) : e x = e0 x - e0 p := by simp [e,sub_eq_add_neg]
  have hezero : e p = 0 := by simp [heval]
  obtain ⟨r₀,hr₀,hr₀half,hgermSource,hgermMeet⟩ :=
    endpoint_germs_from_finite_contacts M a hfinite p hp D hD hpD
  have hr₀1 : r₀ < 1 := by linarith
  let incident : J × Bool → Prop := fun g =>
    (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p
  let α : J × Bool → Interval → S := fun g =>
    (a g.1).val.map ∘ endpointGermParameter g.2 r₀ hr₀ hr₀1
  let L := {g : J × Bool // incident g}
  let γ : L → Interval → Plane := fun g => e ∘ α g.val
  have hsource (g : L) (t : Interval) : α g.val t ∈ e.source := by
    rw [heSource]
    have hd := hgermSource g.val g.property t
    exact ⟨hUchart hd.1,hd⟩
  have hαzero (g : L) : α g.val zeroI = p := by
    cases hb : g.val.2 <;> simpa [α,endpointGermParameter,zeroI,hb,incident] using g.property
  have hγ (g : L) : Topology.IsClosedEmbedding (γ g) := by
    have hα := actual_endpoint_germ_embedding M (a g.val.1) g.val.2 r₀ hr₀ hr₀1
    have hc : Continuous (γ g) := e.continuousOn.comp_continuous hα.continuous (hsource g)
    exact hc.isClosedEmbedding (fun s t he => hα.injective (e.injOn (hsource g s) (hsource g t) he))
  have hstart (g : L) : γ g zeroI = 0 := by simp only [γ,Function.comp_apply,hαzero,hezero]
  have hmeet (i j : L) (hij : i ≠ j) : range (γ i) ∩ range (γ j) = {0} := by
    have hreal := hgermMeet i.val j.val (fun he => hij (Subtype.ext he)) i.property j.property
    ext x
    constructor
    · rintro ⟨⟨s,hs⟩,⟨t,ht⟩⟩
      have he : α i.val s = α j.val t := e.injOn (hsource i s) (hsource j t) (hs.trans ht.symm)
      have hz : α i.val s = p := by
        have hh : α i.val s ∈ range (α i.val) ∩ range (α j.val) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hreal] at hh
        exact hh
      exact mem_singleton_iff.mpr (hs.symm.trans ((congrArg e hz).trans hezero))
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      exact ⟨⟨zeroI,hstart i⟩,⟨zeroI,hstart j⟩⟩
  let l₀ : L := ⟨g₀,hg₀⟩
  have hStar : ∃ star : RadializedStar γ 0 e.target,
      ∀ hi : incident (g₀.1,!g₀.2), star.vector ⟨(g₀.1,!g₀.2),hi⟩ = -star.vector l₀ := by
    have htarget0 : (0 : Plane) ∈ e.target := hezero ▸ e.map_source hep
    by_cases hi : incident (g₀.1,!g₀.2)
    · let l₁ : L := ⟨(g₀.1,!g₀.2),hi⟩
      have hne : l₀ ≠ l₁ := by
        intro he
        have hh := congrArg (fun l : L => l.val.2) he
        change g₀.2 = !g₀.2 at hh
        simpa using hh
      obtain ⟨star,hpair⟩ := prescribed_pair_finite_actual_star_radialization_zero γ hγ hstart hmeet
        l₀ l₁ hne e.target e.open_target htarget0
      exact ⟨star,fun _ => hpair⟩
    · obtain ⟨star⟩ := finite_actual_star_radialization γ 0 hγ hstart hmeet
        e.target e.open_target htarget0
      exact ⟨star,fun hi' => (hi hi').elim⟩
  obtain ⟨star,hpair⟩ := hStar
  have small (s : Finset L) : ∃ d : ℝ, 0 < d ∧ d < 1 ∧ ∀ g ∈ s, d < (star.cut g).val := by
    induction s using Finset.induction_on with
    | empty => exact ⟨1/2,by norm_num,by norm_num,by simp⟩
    | @insert g s hg ih =>
      obtain ⟨d,hd,hd1,hds⟩ := ih
      refine ⟨min d ((star.cut g).val/2),lt_min hd (half_pos (star.cut_pos g)),
        (min_le_left _ _).trans_lt hd1,?_⟩
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact (min_le_right _ _).trans_lt (by linarith [star.cut_pos k])
      · exact (min_le_left _ _).trans_lt (hds k hk)
  obtain ⟨d,hd,hd1,hds⟩ := small Finset.univ
  let q : Interval := ⟨d,⟨hd.le,hd1.le⟩⟩
  let r := r₀*d
  have hr : 0 < r := mul_pos hr₀ hd
  have hrhalf : r < 1/2 := by
    have hh : r₀*d < r₀ := by nlinarith
    exact hh.trans hr₀half
  let F : OpenPartialHomeomorph S Plane := e.trans star.H.toOpenPartialHomeomorph
  have hFsource : F.source = e.source := by simp [F]
  have hFval (x : S) : F x = star.H (e x) := rfl
  let v : J × Bool → Plane := fun g => if hi : incident g then star.H (γ ⟨g,hi⟩ q) else 0
  have hv (g : L) : v g.val = star.H (γ g q) := by simp only [v,dif_pos g.property]; rfl
  have hprefix (g : L) :
      star.H '' armPrefix γ g q = segment ℝ (0 : Plane) (v g.val) ∧ v g.val ≠ 0 := by
    obtain ⟨hs,hn⟩ := radialized_prefix_common_cut (γ g) (hγ g) 0 (hstart g) star.H star.fixes_center
      (star.cut g) q hd (hds g (Finset.mem_univ _)).le (star.vector g) (star.vector_nonzero g)
      (by simpa only [zero_add,armPrefix] using star.prefix_image g)
    simpa only [hv,armPrefix] using And.intro hs hn
  let k : Interval → Interval := fun t => ⟨d*t.val,by
    constructor
    · exact mul_nonneg hd.le t.property.1
    · nlinarith [t.property.2]⟩
  have hkRange : range k = {t : Interval | t.val ≤ d} := by
    ext t
    constructor
    · rintro ⟨u,rfl⟩
      change d*u.val ≤ d
      nlinarith [u.property.2]
    · intro ht
      let u : Interval := ⟨t.val/d,⟨div_nonneg t.property.1 hd.le,(div_le_one hd).mpr ht⟩⟩
      refine ⟨u,?_⟩
      apply Subtype.ext
      change d*(t.val/d) = t.val
      field_simp
  have hparam (g : L) : (a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith) = α g.val ∘ k := by
    funext t
    change (a g.val.1).val.map _ = (a g.val.1).val.map _
    congr 1
    apply Subtype.ext
    cases hb : g.val.2 <;> dsimp [endpointGermParameter,α,k,r] <;> ring
  have himage (g : L) :
      range (F ∘ (a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith)) =
        segment ℝ (0 : Plane) (v g.val) := by
    rw [← (hprefix g).1]
    change range (F ∘ ((a g.val.1).val.map ∘ endpointGermParameter g.val.2 r hr (by linarith))) = _
    rw [hparam]
    change range ((star.H ∘ γ g) ∘ k) = _
    rw [range_comp,hkRange]
    exact Set.image_comp star.H (γ g) {t : Interval | t.val ≤ d}
  refine ⟨F,hFsource.symm ▸ hep,?_,?_,?_,r,hr,hrhalf,v,?_,?_,?_,?_⟩
  · rw [hFval,hezero,star.fixes_center]
  · intro x hx
    exact (heSource ▸ (hFsource ▸ hx)).2.2
  · ext x
    constructor
    · rintro ⟨hx,hm⟩
      exact hmarks x hm (heSource ▸ (hFsource ▸ hx)).2.1
    · intro hx
      have hx0 : x = p := hx
      subst x
      exact ⟨hFsource.symm ▸ hep,hp⟩
  · intro g hi
    exact (hprefix ⟨g,hi⟩).2
  · intro hi
    let l₁ : L := ⟨(g₀.1,!g₀.2),hi⟩
    have hmember (g : L) : v g.val ∈ segment ℝ (0 : Plane) (star.vector g) := by
      rw [← zero_add (star.vector g),← star.prefix_image g]
      exact ⟨γ g q,⟨q,(hds g (Finset.mem_univ _)).le,rfl⟩,by rw [hv]⟩
    have hmem0 := hmember l₀
    have hmem1 := hmember l₁
    rw [hpair hi] at hmem1
    rw [segment_eq_image_lineMap] at hmem0 hmem1
    obtain ⟨t,ht,htv⟩ := hmem0
    obtain ⟨s,hs,hsv⟩ := hmem1
    have ht0 : 0 < t := by
      have hn : t ≠ 0 := by
        intro he
        apply (hprefix l₀).2
        simpa [AffineMap.lineMap_apply_module,he] using htv.symm
      exact lt_of_le_of_ne ht.1 (Ne.symm hn)
    have hs0 : 0 < s := by
      have hn : s ≠ 0 := by
        intro he
        apply (hprefix l₁).2
        simpa [AffineMap.lineMap_apply_module,he] using hsv.symm
      exact lt_of_le_of_ne hs.1 (Ne.symm hn)
    refine ⟨s/t,div_pos hs0 ht0,?_⟩
    have htEq : v g₀ = t • star.vector l₀ := by simpa [AffineMap.lineMap_apply_module] using htv.symm
    have hsEq : v (g₀.1,!g₀.2) = -s • star.vector l₀ := by simpa [AffineMap.lineMap_apply_module,smul_neg,neg_smul] using hsv.symm
    rw [htEq,hsEq,smul_smul]
    congr 1
    field_simp
  · intro g j hi hj hgj
    let l : L := ⟨g,hi⟩
    let m : L := ⟨j,hj⟩
    rw [← (hprefix l).1,← (hprefix m).1]
    ext x
    constructor
    · rintro ⟨⟨_,⟨s,hs,rfl⟩,hxs⟩,⟨_,⟨t,ht,rfl⟩,hxt⟩⟩
      have he : γ l s = γ m t := star.H.injective (hxs.trans hxt.symm)
      have hz : γ l s = 0 := by
        have hh : γ l s ∈ range (γ l) ∩ range (γ m) := ⟨⟨s,rfl⟩,⟨t,he.symm⟩⟩
        rw [hmeet l m (fun hh => hgj (congrArg Subtype.val hh))] at hh
        exact hh
      apply mem_singleton_iff.mpr
      exact hxs.symm.trans ((congrArg star.H hz).trans star.fixes_center)
    · intro hx
      have hx0 : x = 0 := hx
      subst x
      exact ⟨⟨γ l zeroI,⟨zeroI,hd.le,rfl⟩,(congrArg star.H (hstart l)).trans star.fixes_center⟩,
        ⟨γ m zeroI,⟨zeroI,hd.le,rfl⟩,(congrArg star.H (hstart m)).trans star.fixes_center⟩⟩
  · intro g hi
    let l : L := ⟨g,hi⟩
    refine ⟨?_,himage l⟩
    rw [hparam l]
    rintro _ ⟨t,rfl⟩
    exact hFsource.symm ▸ hsource l (k t)
end CurveComplex.HyperellipticModel
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
noncomputable local instance markedEndpointRemainderDecidableEq : DecidableEq S := Classical.decEq _
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

 theorem marked_endpoint_compact_whole_remainder
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (p : S) (hp : p ∈ M.cover.branch)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2) :
    ∃ K : Set S, IsCompact K ∧ p ∉ K ∧
      a.val.image = K ∪ ⋃ b : Bool,
        if (if b then a.val.map 1 else a.val.map 0) = p then
          Set.range (a.val.map ∘ endpointGermParameter b r hr (by linarith)) else ∅ := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  let T : Set Interval :=
    {t | (a.val.map 0 = p → r ≤ t.val) ∧ (a.val.map 1 = p → t.val ≤ 1-r)}
  have hTc : IsClosed T := by
    dsimp [T]
    by_cases h0 : a.val.map 0 = p <;> by_cases h1 : a.val.map 1 = p <;>
      simp only [h0,h1,forall_const,true_implies,false_implies,and_true,true_and] <;>
      first | exact isClosed_Ici.preimage continuous_subtype_val | exact isClosed_Iic.preimage continuous_subtype_val |
        exact (isClosed_Ici.preimage continuous_subtype_val).inter
          (isClosed_Iic.preimage continuous_subtype_val) | exact isClosed_univ
  let K := a.val.map '' T
  have hKc : IsCompact K := hTc.isCompact.image a.val.continuous
  have hpK : p ∉ K := by
    rintro ⟨t,ht,he⟩
    obtain ht0 | ht1 := a.val.marked_only_at_ends t (he ▸ hp)
    · subst t
      have hh := ht.1 he
      change r ≤ 0 at hh
      linarith
    · subst t
      have hh := ht.2 he
      change 1 ≤ 1-r at hh
      linarith
  refine ⟨K,hKc,hpK,?_⟩
  apply Set.Subset.antisymm
  · rintro x ⟨t,rfl⟩
    by_cases ht : t ∈ T
    · exact Or.inl ⟨t,ht,rfl⟩
    · right
      have hfail : (a.val.map 0 = p ∧ t.val < r) ∨
          (a.val.map 1 = p ∧ 1-r < t.val) := by
        simpa only [T,mem_setOf_eq,not_and_or,not_forall,not_le,exists_prop] using ht
      rcases hfail with ⟨h0,htr⟩ | ⟨h1,htr⟩
      · apply Set.mem_iUnion.mpr
        refine ⟨false,?_⟩
        simp only [Bool.false_eq_true,if_false,h0,if_true]
        let u : Interval := ⟨t.val/r,⟨div_nonneg t.property.1 hr.le,
          (div_le_one hr).mpr htr.le⟩⟩
        refine ⟨u,?_⟩
        change a.val.map _ = a.val.map t
        congr 1
        apply Subtype.ext
        change r * (t.val/r) = t.val
        field_simp
      · apply Set.mem_iUnion.mpr
        refine ⟨true,?_⟩
        simp only [if_true,h1]
        let u : Interval := ⟨(1-t.val)/r,⟨div_nonneg (by linarith [t.property.2]) hr.le,
          (div_le_one hr).mpr (by linarith)⟩⟩
        refine ⟨u,?_⟩
        change a.val.map _ = a.val.map t
        congr 1
        apply Subtype.ext
        change 1-r*((1-t.val)/r) = t.val
        field_simp
        <;> ring
  · rintro x (⟨t,ht,rfl⟩ | hx)
    · exact ⟨t,rfl⟩
    · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hx
      by_cases hi : (if b then a.val.map 1 else a.val.map 0) = p
      · rw [if_pos hi] at hb
        obtain ⟨t,rfl⟩ := hb
        exact ⟨endpointGermParameter b r hr (by linarith) t,rfl⟩
      · rw [if_neg hi] at hb
        exact False.elim hb

theorem marked_endpoint_whole_trace_ball
    (M : HyperellipticModel E S) {J : Type} [Fintype J]
    (a : J → EssentialMarkedArc M) (p : S) (hp : p ∈ M.cover.branch)
    (F : OpenPartialHomeomorph S Plane) (hpF : p ∈ F.source) (hFp : F p = 0)
    (r : ℝ) (hr : 0 < r) (hrhalf : r < 1/2)
    (v : J × Bool → Plane)
    (hv : ∀ g, (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p → v g ≠ 0)
    (hsource : ∀ g : J × Bool, (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p →
      Set.range ((a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source)
    (himage : ∀ g : J × Bool, (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p →
      Set.range (F ∘ (a g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
        segment ℝ (0 : Plane) (v g)) :
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : Plane) δ ⊆ F.target ∧
      (∀ g, (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p → δ < ‖v g‖) ∧
      (∀ i y, y ∈ F.source → F y ∈ Metric.ball (0 : Plane) δ →
        (y ∈ (a i).val.image ↔ ∃ b : Bool,
          (if b then (a i).val.map 1 else (a i).val.map 0) = p ∧
          F y ∈ segment ℝ (0 : Plane) (v (i,b)))) := by
  classical
  letI : T2Space S := M.sphere.symm.t2Space
  have hremainders := fun i => marked_endpoint_compact_whole_remainder M (a i) p hp r hr hrhalf
  choose K hKc hpK hK using hremainders
  let bad : Set S := ⋃ i, K i
  have hbad : IsClosed bad := isClosed_iUnion_of_finite (fun i => (hKc i).isClosed)
  have hpbad : p ∉ bad := by simpa only [bad,Set.mem_iUnion,not_exists] using hpK
  let U := F.source ∩ badᶜ
  have hU : IsOpen U := F.open_source.inter hbad.isOpen_compl
  have hUF : U ⊆ F.source := fun _ h => h.1
  have hplane : IsOpen (F '' U) := F.isOpen_image_of_subset_source hU hUF
  have hzero : (0 : Plane) ∈ F '' U := ⟨p,⟨hpF,hpbad⟩,hFp⟩
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp hplane 0 hzero
  have small (s : Finset (J × Bool)) : ∃ d : ℝ, 0 < d ∧ d < ε ∧
      ∀ g ∈ s, (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p → d < ‖v g‖ := by
    induction s using Finset.induction_on with
    | empty => exact ⟨ε/2,half_pos hε,by linarith,by simp⟩
    | @insert g s hg ih =>
      obtain ⟨d,hd,hdε,hds⟩ := ih
      by_cases hi : (if g.2 then (a g.1).val.map 1 else (a g.1).val.map 0) = p
      · have hn : 0 < ‖v g‖ := norm_pos_iff.mpr (hv g hi)
        refine ⟨min d (‖v g‖/2),lt_min hd (half_pos hn),
          (min_le_left _ _).trans_lt hdε,?_⟩
        intro k hk hki
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact (min_le_right _ _).trans_lt (by linarith)
        · exact (min_le_left _ _).trans_lt (hds k hk hki)
      · refine ⟨d,hd,hdε,?_⟩
        intro k hk hki
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact (hi hki).elim
        · exact hds k hk hki
  obtain ⟨δ,hδ,hδε,hδv⟩ := small Finset.univ
  have hδball : Metric.ball (0 : Plane) δ ⊆ F '' U :=
    (Metric.ball_subset_ball hδε.le).trans hball
  refine ⟨δ,hδ,?_,fun g hi => hδv g (Finset.mem_univ _) hi,?_⟩
  · intro z hz
    obtain ⟨y,hy,rfl⟩ := hδball hz
    exact F.map_source hy.1
  · intro i y hy hz
    have hybad : y ∉ bad := by
      obtain ⟨x,hx,hxy⟩ := hδball hz
      have he : x = y := F.injOn hx.1 hy hxy
      exact he ▸ hx.2
    constructor
    · intro hya
      rw [hK i] at hya
      rcases hya with hyK | hyG
      · exact (hybad (Set.mem_iUnion.mpr ⟨i,hyK⟩)).elim
      · obtain ⟨b,hb⟩ := Set.mem_iUnion.mp hyG
        by_cases hi : (if b then (a i).val.map 1 else (a i).val.map 0) = p
        · rw [if_pos hi] at hb
          obtain ⟨t,ht⟩ := hb
          refine ⟨b,hi,?_⟩
          rw [← himage (i,b) hi]
          exact ⟨t,congrArg F ht⟩
        · rw [if_neg hi] at hb
          exact hb.elim
    · rintro ⟨b,hi,hb⟩
      rw [← himage (i,b) hi] at hb
      obtain ⟨t,ht⟩ := hb
      have he : (a i).val.map (endpointGermParameter b r hr (by linarith) t) = y :=
        F.injOn (hsource (i,b) hi ⟨t,rfl⟩) hy ht
      exact ⟨endpointGermParameter b r hr (by linarith) t,he⟩
end CurveComplex.HyperellipticModel
open Set Topology Schoenflies
open CurveComplex.ArcFinitePosition

private noncomputable def negativeSlopeHomeomorph (ell : ℝ) (hell : 0 < ell) : ℝ ≃ₜ ℝ := by
  classical
  let f : ℝ → ℝ := fun x => if 0 ≤ x then x else x/ell
  let g : ℝ → ℝ := fun x => if 0 ≤ x then x else x*ell
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_,
           continuous_toFun := ?_, continuous_invFun := ?_ }
  · intro x
    dsimp [f,g]
    by_cases hx : 0 ≤ x
    · simp [hx]
    · have hx' : ¬0 ≤ x/ell := not_le.mpr (div_neg_of_neg_of_pos (lt_of_not_ge hx) hell)
      simp [hx,hx',ne_of_gt hell]
  · intro x
    dsimp [f,g]
    by_cases hx : 0 ≤ x
    · simp [hx]
    · have hx' : ¬0 ≤ x*ell := not_le.mpr (mul_neg_of_neg_of_pos (lt_of_not_ge hx) hell)
      simp [hx,hx',ne_of_gt hell]
  · exact continuous_if_le continuous_const continuous_id continuous_id.continuousOn
      (continuous_id.div_const ell).continuousOn (fun x hx => by simp [← hx])
  · exact continuous_if_le continuous_const continuous_id continuous_id.continuousOn
      (continuous_id.mul_const ell).continuousOn (fun x hx => by simp [← hx])

 theorem plane_selected_opposite_ray_normalization
    (u : Plane) (hu : u ≠ 0) (ell : ℝ) (hell : 0 < ell) :
    ∃ N : Plane ≃ₜ Plane, N 0 = 0 ∧
      N u = Plane.mk 1 0 ∧ N (-ell • u) = Plane.mk (-1) 0 ∧
      ∀ (t : ℝ) (ht : 0 ≤ t) (x : Plane), N (t • x) = t • N x := by
  classical
  let P := planeComplexLinearEquiv
  have hPu : P u ≠ 0 := fun he => hu (P.injective (he.trans P.map_zero.symm))
  let A : Plane ≃ₜ Plane :=
    (P.toHomeomorph.trans (Homeomorph.mulRight₀ ((P u)⁻¹) (inv_ne_zero hPu))).trans P.symm.toHomeomorph
  have hA (x : Plane) : P (A x) = P x * (P u)⁻¹ := by simp [A]
  have hunit : P (Plane.mk 1 0) = (1 : ℂ) := by rfl
  have hAzero : A 0 = 0 := by apply P.injective; simp [hA]
  have hAu : A u = Plane.mk 1 0 := by apply P.injective; rw [hA,hunit,mul_inv_cancel₀ hPu]
  have hAsmul (t : ℝ) (x : Plane) : A (t • x) = t • A x := by
    apply P.injective
    simp only [hA,map_smul,Complex.real_smul,mul_assoc]
  let Q : Plane ≃ₜ ℝ × ℝ :=
    ((EuclideanSpace.equiv (Fin 2) ℝ).trans (ContinuousLinearEquiv.finTwoArrow ℝ ℝ)).toHomeomorph
  let B : Plane ≃ₜ Plane :=
    (Q.trans ((negativeSlopeHomeomorph ell hell).prodCongr (Homeomorph.refl ℝ))).trans Q.symm
  have hB (x : Plane) : B x = Plane.mk (if 0 ≤ x 0 then x 0 else x 0 / ell) (x 1) := by rfl
  have hBsmul (t : ℝ) (ht : 0 ≤ t) (x : Plane) : B (t • x) = t • B x := by
    by_cases ht0 : t = 0
    · subst t; simp [hB,Plane.mk]
    have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    have hiff : 0 ≤ t*x 0 ↔ 0 ≤ x 0 := by simpa using (mul_nonneg_iff_of_pos_left htpos)
    rw [hB,hB]
    ext j
    fin_cases j
    · change (if 0 ≤ t*x 0 then t*x 0 else (t*x 0)/ell) =
        t * (if 0 ≤ x 0 then x 0 else x 0 / ell)
      rw [if_congr hiff rfl rfl]
      split_ifs <;> ring
    · simp [Plane.mk]
  let N := A.trans B
  refine ⟨N,?_,?_,?_,?_⟩
  · change B (A 0) = 0
    rw [hAzero,hB]
    simp [Plane.mk]
  · change B (A u) = Plane.mk 1 0
    rw [hAu,hB]
    norm_num [Plane.mk]
  · change B (A (-ell • u)) = Plane.mk (-1) 0
    rw [hAsmul,hAu,hB]
    have he : -ell / ell = (-1 : ℝ) := by field_simp
    simp [Plane.mk,not_le_of_gt hell,he]
  · intro t ht x
    change B (A (t • x)) = t • B (A x)
    rw [hAsmul,hBsmul t ht]

 theorem homogeneous_homeomorph_segment_image
    (N : Plane ≃ₜ Plane) (hN : N 0 = 0)
    (hsmul : ∀ (t : ℝ), 0 ≤ t → ∀ x : Plane, N (t • x) = t • N x)
    (x : Plane) : N '' segment ℝ (0 : Plane) x = segment ℝ (0 : Plane) (N x) := by
  rw [segment_eq_image_lineMap,segment_eq_image_lineMap,Set.image_image]
  apply Set.image_congr
  intro t ht
  simp only [Function.comp_apply,AffineMap.lineMap_apply_module,smul_zero,zero_add]
  exact hsmul t ht.1 x
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
noncomputable local instance markedEndpointFanDecidableEq : DecidableEq S := Classical.decEq _
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]

theorem actual_marked_endpoint_source_fan_chart
    (M : HyperellipticModel E S) {I : Type} [Fintype I]
    (c : I → EssentialMarkedArc M)
    (hfinite : ∀ i j, i ≠ j → (ArcSurgery.crossings M (c i) (c j)).Finite)
    (p : S) (hp : p ∈ M.cover.branch)
    (W : Set S) (hW : IsOpen W) (hpW : p ∈ W)
    (g₀ : I × Bool)
    (hg₀ : (if g₀.2 then (c g₀.1).val.map 1 else (c g₀.1).val.map 0) = p) :
    let incident : I × Bool → Prop := fun g =>
      (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0) = p
    ∃ F : OpenPartialHomeomorph S Plane,
      p ∈ F.source ∧ F p = 0 ∧ F.source ⊆ W ∧
      F.source ∩ (M.cover.branch : Set S) = {p} ∧
    ∃ r : ℝ, ∃ hr : 0 < r, ∃ hrhalf : r < 1/2,
    ∃ v : I × Bool → Plane,
      (∀ g, incident g → v g ≠ 0) ∧
      v g₀ = Plane.mk 1 0 ∧
      (incident (g₀.1,!g₀.2) → v (g₀.1,!g₀.2) = Plane.mk (-1) 0) ∧
      (∀ g, incident g → g ≠ g₀ → v g 1 = 0 → v g 0 ≤ 0) ∧
      (∀ g k, incident g → incident k → g ≠ k →
        segment ℝ (0 : Plane) (v g) ∩ segment ℝ (0 : Plane) (v k) = {0}) ∧
      (∀ g, incident g →
        Set.range ((c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
        Set.range (F ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
          segment ℝ (0 : Plane) (v g)) ∧
    ∃ δ : ℝ, 0 < δ ∧ Metric.ball (0 : Plane) δ ⊆ F.target ∧
      (∀ g, incident g → δ < ‖v g‖) ∧
      (∀ i y, y ∈ F.source → F y ∈ Metric.ball (0 : Plane) δ →
        (y ∈ (c i).val.image ↔
          ∃ b : Bool, incident (i,b) ∧ F y ∈ segment ℝ (0 : Plane) (v (i,b)))) ∧
      (∀ i, ∃ K : Set S, IsCompact K ∧ p ∉ K ∧
        (c i).val.image = K ∪
          ⋃ b : Bool, if incident (i,b) then
            Set.range ((c i).val.map ∘ endpointGermParameter b r hr (by linarith)) else ∅) := by
  classical
  dsimp only
  let incident : I × Bool → Prop := fun g =>
    (if g.2 then (c g.1).val.map 1 else (c g.1).val.map 0) = p
  obtain ⟨e,hpe,hep,heW,hemarks,r,hr,hrhalf,v,hvn,hopp,hmeet,hgerms⟩ :=
    marked_endpoint_source_fan_unnormalized M c hfinite p hp W hW hpW g₀ hg₀
  have hex : ∃ ell : ℝ, 0 < ell ∧
      (incident (g₀.1,!g₀.2) → v (g₀.1,!g₀.2) = -ell • v g₀) := by
    by_cases hi : incident (g₀.1,!g₀.2)
    · obtain ⟨ell,hell,he⟩ := hopp hi
      exact ⟨ell,hell,fun _ => he⟩
    · exact ⟨1,by norm_num,fun hi' => (hi hi').elim⟩
  obtain ⟨ell,hell,hop⟩ := hex
  obtain ⟨N,hNzero,hNunit,hNopp,hNsmul⟩ :=
    plane_selected_opposite_ray_normalization (v g₀) (hvn g₀ hg₀) ell hell
  let F : OpenPartialHomeomorph S Plane := e.trans N.toOpenPartialHomeomorph
  let w : I × Bool → Plane := N ∘ v
  have hFs : F.source = e.source := by simp [F]
  have hFval (x : S) : F x = N (e x) := rfl
  have hw0 : w g₀ = Plane.mk 1 0 := hNunit
  have hwn (g : I × Bool) (hi : incident g) : w g ≠ 0 := by
    intro he
    exact hvn g hi (N.injective (he.trans hNzero.symm))
  have hseg (g : I × Bool) : N '' segment ℝ (0 : Plane) (v g) = segment ℝ (0 : Plane) (w g) :=
    homogeneous_homeomorph_segment_image N hNzero hNsmul (v g)
  have hwmeet (g k : I × Bool) (hg : incident g) (hk : incident k) (hne : g ≠ k) :
      segment ℝ (0 : Plane) (w g) ∩ segment ℝ (0 : Plane) (w k) = {0} := by
    rw [← hseg g,← hseg k,← Set.image_inter N.injective,hmeet g k hg hk hne]
    simp [hNzero]
  have hwhole (g : I × Bool) (hi : incident g) :
      Set.range ((c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) ⊆ F.source ∧
      Set.range (F ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith)) =
        segment ℝ (0 : Plane) (w g) := by
    refine ⟨fun x hx => hFs.symm ▸ (hgerms g hi).1 hx,?_⟩
    change range (N ∘ (e ∘ (c g.1).val.map ∘ endpointGermParameter g.2 r hr (by linarith))) = _
    rw [Set.range_comp,(hgerms g hi).2,hseg]
  have hwhorizontal (g : I × Bool) (hi : incident g) (hne : g ≠ g₀)
      (hy : w g 1 = 0) : w g 0 ≤ 0 := by
    by_contra hn
    have hx : 0 < w g 0 := lt_of_not_ge hn
    let t := min (w g 0) 1 / 2
    have ht : 0 < t := half_pos (lt_min hx (by norm_num))
    have htg : t ≤ w g 0 := by dsimp [t]; linarith [min_le_left (w g 0) 1]
    have ht1 : t ≤ 1 := by dsimp [t]; linarith [min_le_right (w g 0) 1]
    let z : Plane := Plane.mk t 0
    have hzunit : z ∈ segment ℝ (0 : Plane) (w g₀) := by
      rw [hw0,segment_eq_image_lineMap]
      refine ⟨t,⟨ht.le,ht1⟩,?_⟩
      ext j
      fin_cases j <;> simp [z,Plane.mk,AffineMap.lineMap_apply_module]
    have hzg : z ∈ segment ℝ (0 : Plane) (w g) := by
      rw [segment_eq_image_lineMap]
      refine ⟨t / w g 0,⟨div_nonneg ht.le hx.le,(div_le_one hx).mpr htg⟩,?_⟩
      ext j
      fin_cases j
      · simp only [AffineMap.lineMap_apply_module,smul_zero,zero_add]
        change (t / w g 0) * w g 0 = t
        field_simp
      · simp [z,Plane.mk,AffineMap.lineMap_apply_module,hy]
    have hzero : z = 0 := by
      have hz : z ∈ segment ℝ (0 : Plane) (w g) ∩ segment ℝ (0 : Plane) (w g₀) := ⟨hzg,hzunit⟩
      rw [hwmeet g g₀ hi hg₀ hne] at hz
      exact hz
    have htzero : t = 0 := congrArg (fun x : Plane => x 0) hzero
    exact (ne_of_gt ht) htzero
  obtain ⟨δ,hδ,hball,hδv,hinc⟩ := marked_endpoint_whole_trace_ball M c p hp F
    (hFs.symm ▸ hpe) (by rw [hFval,hep,hNzero]) r hr hrhalf w hwn
    (fun g hi => (hwhole g hi).1) (fun g hi => (hwhole g hi).2)
  refine ⟨F,hFs.symm ▸ hpe,?_,?_,?_,r,hr,hrhalf,w,hwn,hw0,?_,hwhorizontal,
    hwmeet,hwhole,δ,hδ,hball,hδv,hinc,?_⟩
  · rw [hFval,hep,hNzero]
  · exact hFs ▸ heW
  · rw [hFs]; exact hemarks
  · intro hi
    change N (v (g₀.1,!g₀.2)) = _
    rw [hop hi,hNopp]
  · intro i
    exact marked_endpoint_compact_whole_remainder M (c i) p hp r hr hrhalf
end CurveComplex.HyperellipticModel
