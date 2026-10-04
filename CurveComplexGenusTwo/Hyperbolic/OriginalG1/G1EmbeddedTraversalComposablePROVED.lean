import CurveComplexGenusTwo.Hyperbolic.OriginalG1.ActualParametrizedClosedGeodesicG1GenusTwo
import Mathlib
namespace CurveComplex.Hyperbolic
open Set Filter Topology
open scoped Manifold ContDiff UpperHalfPlane
variable {E : Type} [TopologicalSpace E]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

theorem parametrized_closed_geodesic_has_geodesic_image
    (H : ClosedHyperbolicMetric E) (h : C(Circle, E))
    (hh : letI : MetricSpace E := H.metric; IsParametrizedClosedGeodesic h) :
    letI : MetricSpace E := H.metric
    IsClosedGeodesic (Set.range h) := by
  obtain ⟨path,period,φ,hperiod,hcont,hperiodic,hparam,hunit⟩ := hh
  refine ⟨path,period,hperiod,hcont,hperiodic,?_,hunit⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨t,rfl⟩
    exact ⟨φ (Circle.exp (2 * Real.pi * t / period)),(hparam t).symm⟩
  · rintro _ ⟨z,rfl⟩
    obtain ⟨θ,hθ⟩ := Circle.exp_surjective (φ.symm z)
    let t : ℝ := θ * period / (2 * Real.pi)
    have htime : 2 * Real.pi * t / period = θ := by
      dsimp [t]
      field_simp [hperiod.ne',Real.pi_ne_zero]
    refine ⟨t,?_⟩
    rw [hparam,htime,hθ,φ.apply_symm_apply]




theorem embedded_geodesic_image_has_parametrized_representative
    (H : ClosedHyperbolicMetric E) (c : Curve E)
    (hc : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image) :
    ∃ h : C(Circle, E),
      IsEmbedding h ∧
      FreeHomotopic ⟨c.map, c.embedded.continuous⟩ h ∧
      (letI : MetricSpace E := H.metric; IsParametrizedClosedGeodesic h) ∧
      Set.range h = c.image := by
  classical
  have realInjective (f : ℝ → ℝ) (hf : Continuous f)
      (hloc : ∀ x, ∃ ε : ℝ, 0 < ε ∧ Set.InjOn f (Set.Ioo (x-ε) (x+ε))) :
      Function.Injective f := by
    have hnoMax (g : ℝ → ℝ) (hg : Continuous g)
        (hl : ∀ x, ∃ ε : ℝ, 0 < ε ∧ Set.InjOn g (Set.Ioo (x-ε) (x+ε)))
        (x : ℝ) : ¬ IsLocalMax g x := by
      intro hmax
      obtain ⟨ε,hε,hi⟩ := hl x
      obtain ⟨δ,hδ,hbound⟩ := Metric.eventually_nhds_iff.mp hmax
      let r := min ε δ / 2
      have hr : 0 < r := by dsimp [r]; positivity
      have hrε : r < ε := by dsimp [r]; have := min_le_left ε δ; linarith
      have hrδ : r < δ := by dsimp [r]; have := min_le_right ε δ; linarith
      rcases hg.continuousOn.strictMonoOn_of_injOn_Ioo (by linarith : x-ε < x+ε) hi with hm | ha
      · have hx : x ∈ Ioo (x-ε) (x+ε) := ⟨by linarith,by linarith⟩
        have hy : x+r ∈ Ioo (x-ε) (x+ε) := ⟨by linarith,by linarith⟩
        have h := hm hx hy (by linarith)
        have hb := hbound (y := x+r) (by simpa [Real.dist_eq,abs_of_pos hr] using hrδ)
        exact (not_lt_of_ge hb) h
      · have hx : x ∈ Ioo (x-ε) (x+ε) := ⟨by linarith,by linarith⟩
        have hy : x-r ∈ Ioo (x-ε) (x+ε) := ⟨by linarith,by linarith⟩
        have h := ha hy hx (by linarith)
        have hb := hbound (y := x-r) (by simpa [Real.dist_eq,abs_neg,abs_of_pos hr] using hrδ)
        exact (not_lt_of_ge hb) h
    have hn : ∀ x, ¬ IsLocalMax f x := hnoMax f hf hloc
    have hnneg : ∀ x, ¬ IsLocalMax (fun t => -f t) x := by
      apply hnoMax _ hf.neg
      intro x
      obtain ⟨ε,hε,hi⟩ := hloc x
      exact ⟨ε,hε,fun a ha b hb h => hi ha hb (neg_injective h)⟩
    have hordered (a b : ℝ) (hab : a < b) (he : f a=f b) : False := by
      let m := (a+b)/2
      have hm : m ∈ Ioo a b := ⟨by dsimp [m]; linarith,by dsimp [m]; linarith⟩
      obtain ⟨ε,hε,hi⟩ := hloc m
      let d := min ε (b-m) / 2
      have hd : 0 < d := by dsimp [d]; exact div_pos (lt_min hε (sub_pos.mpr hm.2)) (by norm_num)
      have hdε : d < ε := by dsimp [d]; have := min_le_left ε (b-m); linarith
      have hdb : d < b-m := by dsimp [d]; have := min_le_right ε (b-m); have := hm.2; linarith
      have hm' : m ∈ Ioo (m-ε) (m+ε) := ⟨by linarith,by linarith⟩
      have hv' : m+d ∈ Ioo (m-ε) (m+ε) := ⟨by linarith,by linarith⟩
      have hne : f m ≠ f (m+d) := fun h => (ne_of_lt (by linarith : m < m+d)) (hi hm' hv' h)
      have hex : ∃ z ∈ Ioo a b, f z ≠ f a := by
        by_cases hma : f m=f a
        · exact ⟨m+d,⟨by linarith [hm.1],by linarith [hm.2]⟩,fun h => hne (hma.trans h.symm)⟩
        · exact ⟨m,hm,hma⟩
      obtain ⟨z,hz,hza⟩ := hex
      have hends (y : ℝ) (hy : y ∈ Icc a b \ Ioo a b) : y=a ∨ y=b := by
        simp only [mem_diff,mem_Icc,mem_Ioo,not_and_or,not_lt] at hy
        rcases hy.2 with ha | hb
        · exact Or.inl (le_antisymm ha hy.1.1)
        · exact Or.inr (le_antisymm hy.1.2 hb)
      rcases lt_or_gt_of_ne hza with hzlt | hzgt
      · obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isLocalMax_mem_open Ioo_subset_Icc_self
          hf.neg.continuousOn (Ioo_subset_Icc_self hz) (by
            intro y hy
            change -f y < -f z
            rcases hends y hy with hya | hyb
            · rw [hya]; linarith
            · rw [hyb,←he]; linarith) isOpen_Ioo
        exact hnneg x hmax
      · obtain ⟨x,hx,hmax⟩ := isCompact_Icc.exists_isLocalMax_mem_open Ioo_subset_Icc_self
          hf.continuousOn (Ioo_subset_Icc_self hz) (by
            intro y hy; rcases hends y hy with hya | hyb
            · rw [hya]; linarith
            · rw [hyb,←he]; linarith) isOpen_Ioo
        exact hn x hmax
    intro a b he
    rcases lt_trichotomy a b with hab | rfl | hba
    · exact False.elim (hordered a b hab he)
    · rfl
    · exact False.elim (hordered b a hba he.symm)
  have periodicLiftHomeomorphism (f : C(ℝ,ℝ)) (hfi : Function.Injective f) (P : ℝ) (hP : 0 < P)
      (hexp : Function.Periodic (fun t => Circle.exp (f t)) P) :
      ∃ e : ℝ ≃ₜ ℝ, ∀ t, e t=f t := by
    obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp (hexp 0)
    have hdrift : ∀ t : ℝ, f (t+P)=f t+(n:ℝ)*(2*Real.pi) := by
      have hh : (fun t : ℝ => f (t+P)) = (fun t => f t+(n:ℝ)*(2*Real.pi)) := by
        refine Circle.isCoveringMap_exp.eq_of_comp_eq
          (f.continuous.comp (continuous_id.add continuous_const))
          (f.continuous.add continuous_const) ?_ 0 ?_
        · funext t
          change Circle.exp (f (t+P))=Circle.exp (f t+(n:ℝ)*(2*Real.pi))
          rw [show Circle.exp (f (t+P))=Circle.exp (f t) from hexp t,Circle.exp_add,Circle.exp_int_mul_two_pi,mul_one]
        · simpa only [zero_add] using hn
      exact fun t => congrFun hh t
    let D : ℝ := (n:ℝ)*(2*Real.pi)
    have hD : D ≠ 0 := by
      intro hz
      have hh := hdrift 0
      change f (0+P)=f 0+D at hh
      rw [hz,add_zero,zero_add] at hh
      exact hP.ne' (hfi hh)
    let err (t : ℝ) := f t-D/P*t
    have herr : Function.Periodic err P := by
      intro t; dsimp [err,D]; rw [hdrift]
      field_simp [hP.ne'] <;> ring
    have hmul (k : ℤ) : f ((k:ℝ)*P)=f 0+(k:ℝ)*D := by
      have hh := herr.zsmul k 0
      simp only [zsmul_eq_mul,zero_add] at hh
      dsimp [err] at hh
      have hp : D/P*((k:ℝ)*P)=(k:ℝ)*D := by field_simp [hP.ne']
      rw [hp,mul_zero,sub_zero] at hh
      linarith
    have hfs : Function.Surjective f := by
      intro y
      obtain ⟨k,hk⟩ := exists_int_gt ((y-f 0)/|D|)
      obtain ⟨j,hj⟩ := exists_int_lt ((y-f 0)/|D|)
      have habs : 0 < |D| := abs_pos.mpr hD
      have hupper : y < f 0+(k:ℝ)*|D| := by
        have := (div_lt_iff₀ habs).mp hk
        linarith
      have hlower : f 0+(j:ℝ)*|D| < y := by
        have := (lt_div_iff₀ habs).mp hj
        linarith
      rcases le_or_gt 0 D with hpos | hneg
      · rw [abs_of_nonneg hpos] at hupper hlower
        obtain ⟨t,ht⟩ := intermediate_value_univ ((j:ℝ)*P) ((k:ℝ)*P) f.continuous
          (by rw [hmul,hmul]; exact ⟨hlower.le,hupper.le⟩)
        exact ⟨t,ht⟩
      · rw [abs_of_neg hneg] at hupper hlower
        obtain ⟨t,ht⟩ := intermediate_value_univ (((-j:ℤ):ℝ)*P) (((-k:ℤ):ℝ)*P) f.continuous
          (by rw [hmul,hmul]; simp only [Int.cast_neg]; constructor <;> nlinarith)
        exact ⟨t,ht⟩
    rcases f.continuous.strictMono_of_inj hfi with hm | ha
    · let e := (hm.orderIsoOfSurjective f hfs).toHomeomorph
      exact ⟨e,fun _ => rfl⟩
    · let e := (StrictMono.orderIsoOfSurjective (β := ℝᵒᵈ) f ha hfs).toHomeomorph
      exact ⟨{ e with toEquiv := e.toEquiv },fun _ => rfl⟩
  have primitiveShift {E : Type} [MetricSpace E] (path : ℝ → E) (e : ℝ ≃ₜ ℝ)
      (hpath : ∀ s t, path s=path t ↔ Circle.exp (e s)=Circle.exp (e t))
      (hunit : ∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s u, |s-t|<ε → |u-t|<ε →
        dist (path s) (path u)=|s-u|) :
      ∃ L : ℝ, L ≠ 0 ∧ Function.Periodic path L ∧
        (∀ t, e (t+L)=e t+2*Real.pi) ∧
        ∀ s t, path s=path t → ∃ n : ℤ, s-t=(n:ℝ)*L := by
    classical
    let τ : ℝ ≃ₜ ℝ := (e.trans (Homeomorph.addRight (2*Real.pi))).trans e.symm
    have heτ (t : ℝ) : e (τ t)=e t+2*Real.pi := by
      change e (e.symm (e t+2*Real.pi))=e t+2*Real.pi
      exact e.apply_symm_apply _
    have hτpath (t : ℝ) : path (τ t)=path t := by
      apply (hpath _ _).mpr
      rw [heτ,Circle.exp_add_two_pi]
    have hτmono : StrictMono τ := by
      rcases e.continuous.strictMono_of_inj e.injective with hm | ha
      · intro a b hab
        apply hm.lt_iff_lt.mp
        rw [heτ,heτ]
        have := hm hab
        linarith
      · intro a b hab
        by_contra hn
        have hle := ha.antitone (le_of_not_gt hn)
        rw [heτ,heτ] at hle
        have := ha hab
        linarith
    have hdifference : IsLocallyConstant (fun t : ℝ => τ t-t) := by
      apply (IsLocallyConstant.iff_eventually_eq _).mpr
      intro t
      obtain ⟨ε,hε,hu⟩ := hunit t
      obtain ⟨η,hη,hv⟩ := hunit (τ t)
      have hn : ∀ᶠ s in 𝓝 t, |τ s-τ t|<η := by
        exact τ.continuous.continuousAt.eventually
          (Metric.ball_mem_nhds (τ t) hη) |>.mono (fun s hs => by simpa [Metric.mem_ball,Real.dist_eq] using hs)
      have hs : ∀ᶠ s in 𝓝 t, |s-t|<ε := by
        exact Filter.mem_of_superset (Metric.ball_mem_nhds t hε)
          (fun s hs => by change |s-t|<ε; simpa only [Metric.mem_ball,Real.dist_eq] using hs)
      filter_upwards [hn,hs] with s hsn hss
      have heq := hv (τ s) (τ t) hsn (by simpa using hη)
      rw [hτpath,hτpath,hu s t hss (by simpa using hε)] at heq
      rcases le_total t s with hts | hst
      · rw [abs_of_nonneg (sub_nonneg.mpr hts),abs_of_nonneg (sub_nonneg.mpr (hτmono.monotone hts))] at heq
        linarith
      · rw [abs_of_nonpos (sub_nonpos.mpr hst),abs_of_nonpos (sub_nonpos.mpr (hτmono.monotone hst))] at heq
        linarith
    let L : ℝ := τ 0
    have hshift (t : ℝ) : τ t=t+L := by
      have h := congrFun (hdifference.eq_const 0) t
      dsimp [L] at ⊢
      simp only [sub_zero,Function.const_apply] at h
      linarith
    have hL : L ≠ 0 := by
      intro hz
      have h := heτ 0
      change e L=e 0+2*Real.pi at h
      rw [hz] at h
      have := Real.pi_pos
      linarith
    have heL (t : ℝ) : e (t+L)=e t+2*Real.pi := by rw [←hshift]; exact heτ t
    refine ⟨L,hL,?_,heL,?_⟩
    · intro t
      rw [←hshift]
      exact hτpath t
    · intro s t hst
      obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp ((hpath s t).mp hst)
      let err (t : ℝ) := e t-(2*Real.pi)/L*t
      have herr : Function.Periodic err L := by
        intro t; dsimp [err]; rw [heL]
        field_simp [hL] <;> ring
      have hh := herr.zsmul n t
      simp only [zsmul_eq_mul] at hh
      dsimp [err] at hh
      have halg : (2*Real.pi)/L*(t+(n:ℝ)*L)=(2*Real.pi)/L*t+(n:ℝ)*(2*Real.pi) := by
        field_simp [hL] <;> ring
      rw [halg] at hh
      have heq : e (t+(n:ℝ)*L)=e s := by linarith
      have htime := e.injective heq
      exact ⟨n,by linarith⟩
  have minimalCircle {E : Type} [TopologicalSpace E] [T2Space E]
      (path : C(ℝ,E)) (ℓ : ℝ) (hℓ : 0 < ℓ)
      (hperiod : Function.Periodic path ℓ)
      (hfibre : ∀t u : ℝ, path t=path u → ∃n : ℤ, t-u=(n:ℝ)*ℓ) :
      ∃ g : C(Circle,E), IsEmbedding g ∧
        ∀t : ℝ, g (AddCircle.homeomorphCircle hℓ.ne' (t:AddCircle ℓ))=path t := by
    let descended : C(AddCircle ℓ,E) :=
      ⟨hperiod.lift,continuous_coinduced_dom.mpr path.continuous⟩
    have hdesc : Function.Injective descended := by
      intro z w h
      obtain ⟨t,rfl⟩ := QuotientAddGroup.mk_surjective z
      obtain ⟨u,rfl⟩ := QuotientAddGroup.mk_surjective w
      change path t=path u at h
      obtain ⟨n,hn⟩ := hfibre t u h
      apply sub_eq_zero.mp
      rw [←AddCircle.coe_sub]
      apply (AddCircle.coe_eq_zero_iff (p:=ℓ)).mpr
      exact ⟨n,by simpa only [zsmul_eq_mul] using hn.symm⟩
    let coordinate : AddCircle ℓ ≃ₜ Circle := AddCircle.homeomorphCircle hℓ.ne'
    let g : C(Circle,E) := descended.comp ⟨coordinate.symm,coordinate.symm.continuous⟩
    refine ⟨g,?_,?_⟩
    · exact (g.continuous.isClosedEmbedding (hdesc.comp coordinate.symm.injective)).isEmbedding
    · intro t
      change descended (coordinate.symm (coordinate (t:AddCircle ℓ)))=path t
      rw [coordinate.symm_apply_apply]
      rfl
  
  have angularLift (H : ClosedHyperbolicMetric E) (c : Curve E)
      (hc : letI : MetricSpace E := H.metric; IsClosedGeodesic c.image) :
      letI : MetricSpace E := H.metric
      ∃ path : ℝ → E, ∃ period : ℝ, ∃ f : C(ℝ,ℝ),
        0 < period ∧ Continuous path ∧ Function.Periodic path period ∧ Set.range path = c.image ∧
        (∀ t, path t = c.map (Circle.exp (f t))) ∧
        (∀ t, ∃ ε : ℝ, 0 < ε ∧ Set.InjOn f (Ioo (t-ε) (t+ε))) ∧
        (∀ t, ∃ ε : ℝ, 0 < ε ∧ ∀ s u : ℝ, |s-t|<ε → |u-t|<ε →
          dist (path s) (path u)=|s-u|) := by
    classical
    letI : MetricSpace E := H.metric
    obtain ⟨path,period,hperiod,hcont,hper,hrange,hunit⟩ := hc
    have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
      letI : MetricSpace E := H.metric
      infer_instance
    rw [H.compatible] at ht2
    letI : T2Space E := ht2
    let cm : C(Circle,c.image) := ⟨fun z => ⟨c.map z,Set.mem_range_self z⟩,
      c.embedded.continuous.subtype_mk _⟩
    have hcm : Function.Bijective cm := by
      constructor
      · intro z w h; exact c.embedded.injective (congrArg Subtype.val h)
      · rintro ⟨x,z,hz⟩; exact ⟨z,Subtype.ext hz⟩
    let ce : Circle ≃ₜ c.image := (Equiv.ofBijective cm hcm).toHomeomorphOfContinuousClosed
      cm.continuous cm.continuous.isClosedMap
    have hpath (t : ℝ) : path t ∈ c.image := hrange ▸ Set.mem_range_self t
    let α : C(ℝ,Circle) := ⟨fun t => ce.symm ⟨path t,hpath t⟩,
      ce.symm.continuous.comp (hcont.subtype_mk _)⟩
    obtain ⟨a,ha⟩ := Circle.exp_surjective (α 0)
    obtain ⟨f,hf,_⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts α 0 a ha
    have hclock (t : ℝ) : path t = c.map (Circle.exp (f t)) := by
      have hf' : Circle.exp (f t)=α t := congrFun hf.2 t
      rw [hf']
      exact (congrArg Subtype.val (ce.apply_symm_apply ⟨path t,hpath t⟩)).symm
    refine ⟨path,period,f,hperiod,hcont,hper,hrange,hclock,?_,hunit⟩
    intro t
    obtain ⟨ε,hε,hu⟩ := hunit t
    refine ⟨ε,hε,?_⟩
    intro s hs u huu he
    have hpaths : path s=path u := by rw [hclock s,hclock u,he]
    have hs' : |s-t|<ε := abs_lt.mpr ⟨by linarith [hs.1],by linarith [hs.2]⟩
    have hu' : |u-t|<ε := abs_lt.mpr ⟨by linarith [huu.1],by linarith [huu.2]⟩
    have hzero := hu s u hs' hu'
    rw [hpaths,dist_self] at hzero
    exact sub_eq_zero.mp (abs_eq_zero.mp hzero.symm)
  letI : MetricSpace E := H.metric
  obtain ⟨path,period,f,hperiod,hcont,hperiodic,hrange,hclock,hloc,hunit⟩ := angularLift H c hc
  have hfi : Function.Injective f := realInjective f f.continuous hloc
  have hexp : Function.Periodic (fun t => Circle.exp (f t)) period := by
    intro t
    apply c.embedded.injective
    rw [←hclock,←hclock]
    exact hperiodic t
  obtain ⟨e,he⟩ := periodicLiftHomeomorphism f hfi period hperiod hexp
  have hpath (s t : ℝ) : path s=path t ↔ Circle.exp (e s)=Circle.exp (e t) := by
    rw [he,he,hclock s,hclock t]
    exact c.embedded.injective.eq_iff
  obtain ⟨L,hL,hperL,heL,hfibL⟩ := primitiveShift path e hpath hunit
  let P : ℝ := |L|
  have hP : 0 < P := abs_pos.mpr hL
  have hperP : Function.Periodic path P := by
    rcases le_or_gt 0 L with hp | hn
    · simpa only [P,abs_of_nonneg hp] using hperL
    · simpa only [P,abs_of_neg hn] using hperL.neg
  have hfibP (s t : ℝ) (hst : path s=path t) : ∃ n : ℤ, s-t=(n:ℝ)*P := by
    obtain ⟨n,hn⟩ := hfibL s t hst
    rcases le_or_gt 0 L with hp | hm
    · exact ⟨n,by simpa only [P,abs_of_nonneg hp] using hn⟩
    · refine ⟨-n,?_⟩
      simp only [P,abs_of_neg hm,Int.cast_neg,neg_mul_neg]
      exact hn
  have ht2 : @T2Space E H.metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace := by
    infer_instance
  rw [H.compatible] at ht2
  letI : T2Space E := ht2
  obtain ⟨g,hg,hgclock⟩ := minimalCircle ⟨path,hcont⟩ P hP hperP hfibP
  have hgrange : Set.range g=c.image := by
    apply Set.Subset.antisymm
    · rintro _ ⟨z,rfl⟩
      obtain ⟨t,ht⟩ := (AddCircle.homeomorphCircle hP.ne').surjective z
      obtain ⟨u,hu⟩ := QuotientAddGroup.mk_surjective t
      rw [←ht,←hu,hgclock]
      exact hrange ▸ Set.mem_range_self u
    · intro x hx
      obtain ⟨t,ht⟩ := hrange.symm ▸ hx
      exact ⟨AddCircle.homeomorphCircle hP.ne' (t:AddCircle P),(hgclock t).trans ht⟩
  let cg : Circle ≃ₜ c.image := hg.toHomeomorph.trans (Homeomorph.setCongr hgrange)
  let cc : Circle ≃ₜ c.image := c.embedded.toHomeomorph
  let φ : Circle ≃ₜ Circle := cg.trans cc.symm
  have hφ (z : Circle) : c.map (φ z)=g z := by
    have h := cc.apply_symm_apply (cg z)
    exact congrArg Subtype.val h
  have hgexp (t : ℝ) : g (Circle.exp (2*Real.pi*t/P))=path t := by
    have h := hgclock t
    rw [AddCircle.homeomorphCircle_apply,AddCircle.toCircle_apply_mk] at h
    convert h using 2 <;> ring
  let original : C(Circle,E) := ⟨c.map,c.embedded.continuous⟩
  refine ⟨original,c.embedded,?_,?_,rfl⟩
  · exact ⟨original.comp ⟨Prod.fst,continuous_fst⟩,fun _ => rfl,fun _ => rfl⟩
  · refine ⟨path,P,φ,hP,hcont,hperP,?_,hunit⟩
    intro t
    exact (hgexp t).symm.trans (hφ _).symm
end CurveComplex.Hyperbolic
