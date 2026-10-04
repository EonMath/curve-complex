import Schoenflies.Concatenate
import Schoenflies.JordanClosed
import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ClosedHyperbolicCanonicalBridge
import CurveComplexGenusTwo.Topology.IntersectionParity.CrossingChartCoordinates
import Mathlib
import CurveComplexGenusTwo.Foundations.Definitions
import CurveComplexGenusTwo.Topology.ActualGeometryRelease.ActualHyperbolicAxisAllPROVED
import CurveComplexGenusTwo.Hyperbolic.CompactHexagonRegion
import CurveComplexGenusTwo.Topology.TorusStrip.ProperLineSeparationCore


open Set Topology

private theorem uniformly_separated_metric_set_closed
    {P : Type} [MetricSpace P] (S : Set P) (δ : ℝ) (hδ : 0 < δ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → δ ≤ dist x y) : IsClosed S := by
  rw [← closure_subset_iff_isClosed]
  intro z hz
  obtain ⟨y,hy,hyz⟩ := Metric.mem_closure_iff.mp hz (δ/4) (by positivity)
  by_cases he : z=y
  · exact he ▸ hy
  · have hzy : 0 < dist y z := dist_pos.mpr (Ne.symm he)
    obtain ⟨x,hx,hxz⟩ := Metric.mem_closure_iff.mp hz
      (min (δ/4) (dist y z/2)) (lt_min (by positivity) (by positivity))
    have hxzδ : dist z x < δ/4 := hxz.trans_le (min_le_left _ _)
    have hxzy : dist z x < dist y z/2 := hxz.trans_le (min_le_right _ _)
    by_cases hxy : x=y
    · subst x
      rw [dist_comm z y] at hxzy
      linarith
    · have hlow := hsep x hx y hy hxy
      rw [dist_comm z y] at hyz
      have hup := dist_triangle x z y
      rw [dist_comm x z,dist_comm z y] at hup
      linarith

private theorem isometric_cover_orbit_closed
    {P X G : Type} [MetricSpace P] [TopologicalSpace X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : P => k • z)) (y : P) :
    IsClosed (MulAction.orbit G y) := by
  obtain ⟨U,hyU,hdis⟩ := hq.disjoint y
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp hyU
  have hgap (k : G) (hne : k≠1) : δ ≤ dist (k • y) y := by
    by_contra hh
    have hky : k • y ∈ U := hball (Metric.mem_ball.mpr (lt_of_not_ge hh))
    have hy : y ∈ U := mem_of_mem_nhds hyU
    exact hne (hdis k ⟨k • y,⟨y,hy,rfl⟩,hky⟩)
  apply uniformly_separated_metric_set_closed _ δ hδ
  rintro x ⟨k,rfl⟩ z ⟨l,rfl⟩ hne
  have hkl : l⁻¹*k ≠ 1 := by
    intro he
    apply hne
    have : k=l := by simpa using (inv_mul_eq_one.mp he).symm
    rw [this]
  have hh := hgap (l⁻¹*k) hkl
  have he := (hdeck l⁻¹).dist_eq (k • y) (l • y)
  rw [← he]
  simpa only [smul_smul,inv_mul_cancel,one_smul] using hh

private theorem isometric_quotient_cover_hausdorff
    {P X G : Type} [MetricSpace P] [TopologicalSpace X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : P => k • z)) : T2Space X := by
  constructor
  intro x y hxy
  obtain ⟨a,rfl⟩ := hq.surjective x
  obtain ⟨b,rfl⟩ := hq.surjective y
  have ha : a ∈ (MulAction.orbit G b)ᶜ := by
    intro ha
    exact hxy (hq.apply_eq_iff_mem_orbit.mpr ha)
  have hopen := (isometric_cover_orbit_closed q hq hdeck b).isOpen_compl
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hopen.mem_nhds ha)
  refine ⟨q '' Metric.ball a (r/3),q '' Metric.ball b (r/3),
    hq.isCoveringMap.isOpenMap _ Metric.isOpen_ball,
    hq.isCoveringMap.isOpenMap _ Metric.isOpen_ball,
    ⟨a,Metric.mem_ball_self (by positivity),rfl⟩,
    ⟨b,Metric.mem_ball_self (by positivity),rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨a',ha',haz⟩ ⟨b',hb',hbz⟩
  obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp (haz.trans hbz.symm)
  change k • b' = a' at hk
  have hnear : k • b ∈ Metric.ball a r := by
    apply Metric.mem_ball.mpr
    have ha'd := Metric.mem_ball.mp ha'
    have hb'd := Metric.mem_ball.mp hb'
    have hd := (hdeck k).dist_eq b' b
    rw [hk] at hd
    have htri := dist_triangle (k • b) a' a
    rw [dist_comm (k • b) a',hd] at htri
    linarith
  exact (hball hnear) ⟨k,rfl⟩

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem actual_target_lift_family_contacts
    {P X E G : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace E]
    [Group G] [MulAction G P]
    (p : P → X) (hp : IsQuotientCoveringMap p G) (q : X → E)
    (hq : Function.Injective q) (b : Curve E) (J : ℝ → P)
    (hJ : ∀ t : ℝ, q (p (J t)) = b.map (Circle.exp t)) (z : P) :
    q (p z) ∈ b.image ↔ ∃ k : G, ∃ t : ℝ, z = k • J t := by
  constructor
  · rintro ⟨w,hw⟩
    obtain ⟨t,ht⟩ := Circle.exp_surjective w
    have he : p z = p (J t) := by
      apply hq
      rw [hJ,ht,hw]
    obtain ⟨k,hk⟩ := hp.apply_eq_iff_mem_orbit.mp he
    exact ⟨k,t,hk.symm⟩
  · rintro ⟨k,t,rfl⟩
    rw [hp.map_smul,hJ]
    exact Set.mem_range_self _

-- This is the integer-period/stabilizer construction already checked in G3;
-- it is reproduced mechanically here only to expose its exact local consumer.
private theorem reused_curve_lift_integer_period_and_stabilizer
    {P X E G : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace E]
    [Group G] [MulAction G P]
    (p : P → X) (hp : IsQuotientCoveringMap p G) (q : X → E)
    (c : Curve E) (F : ℝ → P) (g : G)
    (hproj : ∀ s, q (p (F s)) = c.map (Circle.exp s))
    (hperiod : ∀ s, F (s + 2 * Real.pi) = g • F s) :
    (∀ n : ℤ, ∀ s : ℝ, F (s + n * (2 * Real.pi)) = g ^ n • F s) ∧
    (∀ k : G, ∀ s t : ℝ, k • F s = F t → ∃ n : ℤ, k = g ^ n) := by
  letI : IsCancelSMul G P := hp.isCancelSMul
  have hnat (n : ℕ) (s : ℝ) : F (s + n * (2 * Real.pi)) = g ^ n • F s := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : s + (n + 1 : ℕ) * (2 * Real.pi) =
          (s + n * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
      rw [he, hperiod, ih, smul_smul, pow_succ']
  have hint (n : ℤ) (s : ℝ) : F (s + n * (2 * Real.pi)) = g ^ n • F s := by
    cases n with
    | ofNat n => simpa using hnat n s
    | negSucc n =>
      have hh : F s = g ^ (n + 1) • F (s - (n + 1 : ℕ) * (2 * Real.pi)) := by
        convert hnat (n + 1) (s - (n + 1 : ℕ) * (2 * Real.pi)) using 1
        congr 1
        ring
      rw [hh, zpow_negSucc, inv_smul_smul]
      congr 1
      push_cast
      ring
  refine ⟨hint, ?_⟩
  intro k s t hst
  have hcircle : Circle.exp s = Circle.exp t := by
    apply c.embedded.injective
    have hh := congrArg (fun z => q (p z)) hst
    simpa only [hp.map_smul, hproj] using hh
  obtain ⟨n,hn⟩ := Circle.exp_eq_exp.mp hcircle.symm
  refine ⟨n, ?_⟩
  have hh : k • F s = g ^ n • F s := by
    rw [hst, hn, hint]
  exact IsCancelSMul.right_cancel _ _ _ hh

private theorem actual_target_lift_ranges_eq_of_intersection
    {P X E G : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace E]
    [Group G] [MulAction G P]
    (p : P → X) (hp : IsQuotientCoveringMap p G) (q : X → E)
    (b : Curve E) (J : ℝ → P) (g : G)
    (hJ : ∀ t : ℝ, q (p (J t)) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k l : G)
    (hinter : (Set.range (fun t : ℝ => k • J t) ∩
      Set.range (fun t : ℝ => l • J t)).Nonempty) :
    Set.range (fun t : ℝ => k • J t) = Set.range (fun t : ℝ => l • J t) := by
  obtain ⟨z,⟨s,hs⟩,⟨t,ht⟩⟩ := hinter
  have he : (l⁻¹*k) • J s=J t := by
    have hh := congrArg (fun w : P => l⁻¹ • w) (hs.trans ht.symm)
    simpa only [smul_smul,inv_mul_cancel,one_smul] using hh
  have hdata := reused_curve_lift_integer_period_and_stabilizer p hp q b J g hJ hperiod
  obtain ⟨n,hn⟩ := hdata.2 (l⁻¹*k) s t he
  have hk : k=l*g^n := by
    calc
      k=l*(l⁻¹*k) := by simp [←mul_assoc]
      _=l*g^n := congrArg (fun w => l*w) hn
  ext w
  constructor
  · rintro ⟨u,rfl⟩
    refine ⟨u+n*(2*Real.pi),?_⟩
    change l • J (u+n*(2*Real.pi))=k • J u
    rw [hdata.1,hk,mul_smul]
  · rintro ⟨u,rfl⟩
    refine ⟨u-n*(2*Real.pi),?_⟩
    change k • J (u-n*(2*Real.pi))=l • J u
    rw [hk,mul_smul,←hdata.1]
    congr 2
    ring

private theorem actual_distinct_target_lift_ranges_disjoint
    {P X E G : Type} [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace E]
    [Group G] [MulAction G P]
    (p : P → X) (hp : IsQuotientCoveringMap p G) (q : X → E)
    (b : Curve E) (J : ℝ → P) (g : G)
    (hJ : ∀ t : ℝ, q (p (J t)) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k l : G) (hne : Set.range (fun t : ℝ => k • J t) ≠
      Set.range (fun t : ℝ => l • J t)) :
    Disjoint (Set.range (fun t : ℝ => k • J t))
      (Set.range (fun t : ℝ => l • J t)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  by_contra h
  apply hne
  exact actual_target_lift_ranges_eq_of_intersection p hp q b J g hJ hperiod k l
    (Set.nonempty_iff_ne_empty.mpr h)


private theorem actual_lift_family_locally_single
    {P X G : Type} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (b : Curve X) (J : C(ℝ,P))
    (hJ : ∀ t : ℝ, q (J t) = b.map (Circle.exp t))
    (z : P) :
    ∃ V : Set P, IsOpen V ∧ z ∈ V ∧
      (V ∩ q ⁻¹' b.image = ∅ ∨
        ∃ k : G, V ∩ q ⁻¹' b.image ⊆ Set.range (fun t : ℝ => k • J t)) := by
  classical
  have hclosed : IsClosed b.image := (isCompact_range b.embedded.continuous).isClosed
  by_cases hz : q z ∈ b.image
  · obtain ⟨w,hw⟩ := hz
    obtain ⟨t,ht⟩ := Circle.exp_surjective w
    have he : q z = q (J t) := by rw [hJ,ht,hw]
    obtain ⟨k,hk⟩ := hq.apply_eq_iff_mem_orbit.mp he
    change k • J t = z at hk
    obtain ⟨Ω,hΩ,hzΩ,hinj⟩ := hq.isCoveringMap.isLocalHomeomorph.isLocallyInjective z
    let S : Set ℝ := (fun u : ℝ => k • J u) ⁻¹' Ω
    have hS : IsOpen S := hΩ.preimage ((hq.continuous_const_smul k).comp J.continuous)
    have htS : t ∈ S := by change k • J t ∈ Ω; rwa [hk]
    have hC : IsOpen (Circle.exp '' S) := Circle.isCoveringMap_exp.isOpenMap S hS
    obtain ⟨W,hW,himage⟩ := b.embedded.isInducing.image_eq_isOpen_inter_range hC
    have hqw : q z ∈ W := by
      have hm : b.map (Circle.exp t) ∈ b.map '' (Circle.exp '' S) :=
        ⟨Circle.exp t, ⟨t,htS,rfl⟩,rfl⟩
      rw [himage] at hm
      rw [← hJ t,← he] at hm
      exact hm.1
    refine ⟨Ω ∩ q ⁻¹' W,hΩ.inter (hW.preimage hq.continuous),⟨hzΩ,hqw⟩,
      Or.inr ⟨k,?_⟩⟩
    intro y hy
    have hym : q y ∈ b.map '' (Circle.exp '' S) := by
      rw [himage]
      exact ⟨hy.1.2,hy.2⟩
    obtain ⟨w,⟨u,hu,huw⟩,hw⟩ := hym
    refine ⟨u,hinj hu hy.1.1 ?_⟩
    rw [hq.map_smul,hJ,huw,hw]
  · refine ⟨q ⁻¹' b.imageᶜ,hclosed.isOpen_compl.preimage hq.continuous,hz,Or.inl ?_⟩
    simp

private theorem actual_distinct_lift_family_locally_finite
    {P X G : Type} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (b : Curve X) (J : C(ℝ,P)) (g : G)
    (hJ : ∀ t : ℝ, q (J t) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t) :
    LocallyFinite ((↑) : Set.range (fun k : G =>
      Set.range (fun t : ℝ => k • J t)) → Set P) := by
  classical
  let R := fun k : G => Set.range (fun t : ℝ => k • J t)
  have hproj (k : G) {y : P} (hy : y ∈ R k) : q y ∈ b.image := by
    obtain ⟨t,rfl⟩ := hy
    rw [hq.map_smul,hJ]
    exact Set.mem_range_self _
  intro z
  obtain ⟨V,hV,hz,hdata⟩ := actual_lift_family_locally_single q hq b J hJ z
  refine ⟨V,hV.mem_nhds hz,?_⟩
  rcases hdata with hempty | ⟨k,hsub⟩
  · apply Set.finite_empty.subset
    rintro i ⟨y,hy,hVy⟩
    obtain ⟨l,hl⟩ := i.2
    have hyR : y ∈ R l := by
      change R l = (i : Set P) at hl
      rw [hl]
      exact hy
    have hm : y ∈ V ∩ q ⁻¹' b.image := ⟨hVy,hproj l hyR⟩
    rw [hempty] at hm
    exact hm
  · apply (Set.finite_singleton (⟨R k,⟨k,rfl⟩⟩ : Set.range R)).subset
    rintro i ⟨y,hy,hVy⟩
    obtain ⟨l,hl⟩ := i.2
    have hyR : y ∈ R l := by
      change R l = (i : Set P) at hl
      rw [hl]
      exact hy
    have hyk : y ∈ R k := hsub ⟨hVy,hproj l hyR⟩
    have he : R l = R k := actual_target_lift_ranges_eq_of_intersection
      q hq id b J g hJ hperiod l k ⟨y,hyR,hyk⟩
    apply Set.mem_singleton_iff.mpr
    apply Subtype.ext
    exact hl.symm.trans he

private theorem compact_meets_finitely_many_actual_lifts
    {P X G : Type} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (b : Curve X) (J : C(ℝ,P)) (g : G)
    (hJ : ∀ t : ℝ, q (J t) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (K : Set P) (hK : IsCompact K) :
    {L : Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)) |
      ((L : Set P) ∩ K).Nonempty}.Finite := by
  exact (actual_distinct_lift_family_locally_finite q hq b J g hJ hperiod).finite_nonempty_inter_compact hK

private theorem compact_meets_finitely_many_actual_h2_lifts
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (b : Curve X) (J : C(ℝ,H2)) (g : G)
    (hJ : ∀ t : ℝ, q (J t) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (K : Set H2) (hK : IsCompact K) :
    {L : Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)) |
      ((L : Set H2) ∩ K).Nonempty}.Finite := by
  letI : T2Space X := isometric_quotient_cover_hausdorff q hq hdeck
  exact compact_meets_finitely_many_actual_lifts q hq b J g hJ hperiod K hK

private theorem actual_target_lift_contact_local_branch
    {P X G : Type} [TopologicalSpace P] [TopologicalSpace X] [T2Space X]
    [Group G] [MulAction G P]
    (q : P → X) (hq : IsQuotientCoveringMap q G)
    (b : Curve X) (J : C(ℝ,P)) (g : G)
    (hJ : ∀ t : ℝ, q (J t) = b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k : G) (z : P) (hz : z ∈ Set.range (fun t : ℝ => k • J t)) :
    ∃ V : Set P, IsOpen V ∧ z ∈ V ∧
      ∀ x ∈ V, q x ∈ b.image ↔ x ∈ Set.range (fun t : ℝ => k • J t) := by
  have hproj (m : G) (x : P) (hx : x ∈ Set.range (fun t : ℝ => m • J t)) : q x ∈ b.image := by
    obtain ⟨t,rfl⟩ := hx
    rw [hq.map_smul,hJ]
    exact Set.mem_range_self _
  obtain ⟨V,hV,hzV,hdata⟩ := actual_lift_family_locally_single q hq b J hJ z
  refine ⟨V,hV,hzV,?_⟩
  rcases hdata with hempty | ⟨l,hsub⟩
  · have hm : z ∈ V ∩ q ⁻¹' b.image := ⟨hzV,hproj k z hz⟩
    rw [hempty] at hm
    exact False.elim hm
  · have he := actual_target_lift_ranges_eq_of_intersection q hq id b J g hJ hperiod l k
      ⟨z,hsub ⟨hzV,hproj k z hz⟩,hz⟩
    intro x hxV
    constructor
    · intro hxB
      rw [←he]
      exact hsub ⟨hxV,hxB⟩
    · exact hproj k x

end CurveComplex.Hyperbolic

open Set Topology

private theorem actual_chart_rectangle_has_two_connected_arms
    {P : Type} [TopologicalSpace P] (K : OpenPartialHomeomorph P (ℝ × ℝ))
    (z : P) (hz : z ∈ K.source) (hzero : K z=(0,0)) :
    ∃ N A B : Set P, IsOpen N ∧ z ∈ N ∧ N ⊆ K.source ∧
      IsPreconnected A ∧ IsPreconnected B ∧
      A = N ∩ {x | (K x).2<0} ∧ B = N ∩ {x | 0<(K x).2} := by
  have h0target : (0,0) ∈ K.target := hzero ▸ K.map_source hz
  obtain ⟨ρ,hρ,hball⟩ := Metric.mem_nhds_iff.mp (K.open_target.mem_nhds h0target)
  let r : ℝ := ρ/2
  have hr : 0<r := by dsimp [r]; positivity
  let C : Set (ℝ × ℝ) := Set.Ioo (-r) r ×ˢ Set.Ioo (-r) r
  let Cm : Set (ℝ × ℝ) := Set.Ioo (-r) r ×ˢ Set.Ioo (-r) 0
  let Cp : Set (ℝ × ℝ) := Set.Ioo (-r) r ×ˢ Set.Ioo 0 r
  have hC : C ⊆ K.target := by
    intro x hx
    apply hball
    rw [Metric.mem_ball,Prod.dist_eq,Real.dist_eq,Real.dist_eq,sub_zero,sub_zero,max_lt_iff]
    dsimp [C,r] at hx
    constructor <;> rw [abs_lt] <;> constructor <;> linarith [hx.1.1,hx.1.2,hx.2.1,hx.2.2]
  have hmC : Cm ⊆ C := by
    rintro x ⟨hx,hy⟩
    exact ⟨hx,hy.1,hy.2.trans hr⟩
  have hpC : Cp ⊆ C := by
    rintro x ⟨hx,hy⟩
    exact ⟨hx,(neg_lt_zero.mpr hr).trans hy.1,hy.2⟩
  let N : Set P := K.symm '' C
  let A : Set P := K.symm '' Cm
  let B : Set P := K.symm '' Cp
  have hNsource : N ⊆ K.source := by
    rintro _ ⟨x,hx,rfl⟩
    exact K.symm.map_source (hC hx)
  have hNopen : IsOpen N := K.isOpen_image_symm_of_subset_target (isOpen_Ioo.prod isOpen_Ioo) hC
  have hzN : z ∈ N := by
    refine ⟨(0,0),⟨⟨by simpa using neg_lt_zero.mpr hr,hr⟩,
      ⟨by simpa using neg_lt_zero.mpr hr,hr⟩⟩,?_⟩
    rw [←hzero,K.left_inv hz]
  have hAconn : IsPreconnected A :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image K.symm
      (K.symm.continuousOn.mono (hmC.trans hC))
  have hBconn : IsPreconnected B :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image K.symm
      (K.symm.continuousOn.mono (hpC.trans hC))
  refine ⟨N,A,B,hNopen,hzN,hNsource,hAconn,hBconn,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨⟨y,hmC hy,rfl⟩,?_⟩
      change (K (K.symm y)).2<0
      rw [K.right_inv (hC (hmC hy))]
      exact hy.2.2
    · rintro ⟨⟨y,hy,he⟩,hneg⟩
      refine ⟨y,⟨hy.1,hy.2.1,?_⟩,he⟩
      change (K x).2<0 at hneg
      rw [←he,K.right_inv (hC hy)] at hneg
      exact hneg
  · ext x
    constructor
    · rintro ⟨y,hy,rfl⟩
      refine ⟨⟨y,hpC hy,rfl⟩,?_⟩
      change 0<(K (K.symm y)).2
      rw [K.right_inv (hC (hpC hy))]
      exact hy.2.1
    · rintro ⟨⟨y,hy,he⟩,hpos⟩
      refine ⟨y,⟨hy.1,?_,hy.2.2⟩,he⟩
      change 0<(K x).2 at hpos
      rw [←he,K.right_inv (hC hy)] at hpos
      exact hpos

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

private theorem embedded_lift_crossing_chart_coordinate_signs
    {P : Type} [TopologicalSpace P] (F : C(ℝ,P)) (hinj : Function.Injective F)
    (K : OpenPartialHomeomorph P (ℝ × ℝ)) (u : ℝ)
    (huK : F u ∈ K.source) (hzero : K (F u)=(0,0))
    (haxis : ∀ t : ℝ, F t ∈ K.source → (K (F t)).1=0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ v w : ℝ, u-δ<v → v<u → u<w → w<u+δ →
      F v ∈ K.source ∧ F w ∈ K.source ∧
      (((K (F v)).2<0 ∧ 0<(K (F w)).2) ∨
        (0<(K (F v)).2 ∧ (K (F w)).2<0)) := by
  obtain ⟨d,hd,hdK⟩ := Metric.mem_nhds_iff.mp
    (F.continuous.continuousAt.preimage_mem_nhds (K.open_source.mem_nhds huK))
  let δ : ℝ := d/2
  have hδ : 0<δ := by dsimp [δ]; positivity
  let S : Set ℝ := Set.Icc (u-δ) (u+δ)
  have hSK (t : ℝ) (ht : t ∈ S) : F t ∈ K.source := by
    apply hdK
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    dsimp [S,δ] at ht
    constructor <;> linarith [ht.1,ht.2]
  let φ : ℝ → ℝ := fun t => (K (F t)).2
  have hcont : ContinuousOn φ S := continuous_snd.comp_continuousOn
    (K.continuousOn.comp F.continuous.continuousOn hSK)
  have hi : Set.InjOn φ S := by
    intro t ht v hv he
    apply hinj
    apply K.injOn (hSK t ht) (hSK v hv)
    exact Prod.ext ((haxis t (hSK t ht)).trans (haxis v (hSK v hv)).symm) he
  have huS : u ∈ S := ⟨by linarith,by linarith⟩
  have hφzero : φ u=0 := by dsimp [φ]; rw [hzero]
  have hm := hcont.strictMonoOn_of_injOn_Icc' (by linarith : u-δ≤u+δ) hi
  refine ⟨δ,hδ,?_⟩
  intro v w hvl hvu huw hwr
  have hvS : v ∈ S := ⟨hvl.le,by linarith⟩
  have hwS : w ∈ S := ⟨by linarith,hwr.le⟩
  refine ⟨hSK v hvS,hSK w hwS,?_⟩
  rcases hm with hm | hm
  · exact Or.inl ⟨by simpa only [hφzero] using hm hvS huS hvu,
      by simpa only [hφzero] using hm huS hwS huw⟩
  · exact Or.inr ⟨by simpa only [hφzero] using hm hvS huS hvu,
      by simpa only [hφzero] using hm huS hwS huw⟩


private theorem local_connected_arms_opposite_sides
    {X : Type} [TopologicalSpace X] (L U V N A B : Set X) (p x y : X)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (hN : IsOpen N) (hpN : p ∈ N)
    (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (hsplit : N \ L = A ∪ B) (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hx : x ∈ A) (hy : y ∈ B) :
    (x ∈ U ∧ y ∈ V) ∨ (x ∈ V ∧ y ∈ U) := by
  have hAS : A ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact (hsplit.symm ▸ (show z ∈ A ∪ B from Or.inl hz)).2
  have hBS : B ⊆ U ∪ V := by
    intro z hz
    rw [hcover]
    exact (hsplit.symm ▸ (show z ∈ A ∪ B from Or.inr hz)).2
  have hbothU : ¬ (A ⊆ U ∧ B ⊆ U) := by
    rintro ⟨hAU,hBU⟩
    obtain ⟨z,hzN,hzV⟩ := mem_closure_iff.mp hpV N hN hpN
    have hzL : z ∉ L := by
      have : z ∈ U ∪ V := Or.inr hzV
      rw [hcover] at this
      exact this
    have hzAB : z ∈ A ∪ B := hsplit ▸ ⟨hzN,hzL⟩
    exact Set.disjoint_left.mp hdis (hzAB.elim (fun h => hAU h) (fun h => hBU h)) hzV
  have hbothV : ¬ (A ⊆ V ∧ B ⊆ V) := by
    rintro ⟨hAV,hBV⟩
    obtain ⟨z,hzN,hzU⟩ := mem_closure_iff.mp hpU N hN hpN
    have hzL : z ∉ L := by
      have : z ∈ U ∪ V := Or.inl hzU
      rw [hcover] at this
      exact this
    have hzAB : z ∈ A ∪ B := hsplit ▸ ⟨hzN,hzL⟩
    exact Set.disjoint_left.mp hdis hzU (hzAB.elim (fun h => hAV h) (fun h => hBV h))
  rcases hA.subset_or_subset hU hV hdis hAS with hAU | hAV <;>
    rcases hB.subset_or_subset hU hV hdis hBS with hBU | hBV
  · exact False.elim (hbothU ⟨hAU,hBU⟩)
  · exact Or.inl ⟨hAU hx,hBV hy⟩
  · exact Or.inr ⟨hAV hx,hBU hy⟩
  · exact False.elim (hbothV ⟨hAV,hBV⟩)


private theorem actual_embedded_lift_crosses_global_sides
    {P : Type} [TopologicalSpace P] (F : C(ℝ,P)) (hinj : Function.Injective F)
    (L U V : Set P) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V=Lᶜ) (hfrontU : frontier U=L) (hfrontV : frontier V=L)
    (K : OpenPartialHomeomorph P (ℝ × ℝ)) (u : ℝ)
    (huK : F u ∈ K.source) (hzero : K (F u)=(0,0))
    (hsourceaxis : ∀ t : ℝ, F t ∈ K.source → (K (F t)).1=0)
    (htargetaxis : ∀ x ∈ K.source, x ∈ L ↔ (K x).2=0) :
    ∀ r s : ℝ, r<u → u<s →
      ∃ l w : ℝ, r<l ∧ l<u ∧ u<w ∧ w<s ∧
        ((F l ∈ U ∧ F w ∈ V) ∨ (F l ∈ V ∧ F w ∈ U)) := by
  obtain ⟨N,A,B,hN,huN,hNK,hA,hB,hAeq,hBeq⟩ :=
    actual_chart_rectangle_has_two_connected_arms K (F u) huK hzero
  have hsplit : N \ L=A ∪ B := by
    rw [hAeq,hBeq]
    ext x
    constructor
    · rintro ⟨hxN,hxL⟩
      have hn : (K x).2≠0 := fun he => hxL ((htargetaxis x (hNK hxN)).mpr he)
      rcases lt_or_gt_of_ne hn with hn | hn
      · exact Or.inl ⟨hxN,hn⟩
      · exact Or.inr ⟨hxN,hn⟩
    · rintro (⟨hxN,hn⟩ | ⟨hxN,hn⟩)
      · exact ⟨hxN,fun hxL => (ne_of_lt hn) ((htargetaxis x (hNK hxN)).mp hxL)⟩
      · exact ⟨hxN,fun hxL => (ne_of_gt hn) ((htargetaxis x (hNK hxN)).mp hxL)⟩
  have huL : F u ∈ L := (htargetaxis _ huK).mpr (by rw [hzero])
  have huU : F u ∈ closure U := frontier_subset_closure (hfrontU.symm ▸ huL)
  have huV : F u ∈ closure V := frontier_subset_closure (hfrontV.symm ▸ huL)
  obtain ⟨d,hd,hdN⟩ := Metric.mem_nhds_iff.mp
    (F.continuous.continuousAt.preimage_mem_nhds (hN.mem_nhds huN))
  obtain ⟨δ,hδ,hsigns⟩ := embedded_lift_crossing_chart_coordinate_signs F hinj K u huK hzero hsourceaxis
  intro r s hru hus
  let η : ℝ := min d (min δ (min (u-r) (s-u))) / 2
  have hη : 0<η := by dsimp [η]; exact div_pos (lt_min hd (lt_min hδ (lt_min (sub_pos.mpr hru) (sub_pos.mpr hus)))) (by norm_num)
  have hηd : η<d := by dsimp [η]; linarith [min_le_left d (min δ (min (u-r) (s-u)))]
  have hηδ : η<δ := by
    dsimp [η]
    linarith [min_le_right d (min δ (min (u-r) (s-u))),min_le_left δ (min (u-r) (s-u))]
  have hηr : η<u-r := by
    dsimp [η]
    linarith [min_le_right d (min δ (min (u-r) (s-u))),
      min_le_right δ (min (u-r) (s-u)),min_le_left (u-r) (s-u)]
  have hηs : η<s-u := by
    dsimp [η]
    linarith [min_le_right d (min δ (min (u-r) (s-u))),
      min_le_right δ (min (u-r) (s-u)),min_le_right (u-r) (s-u)]
  have hlN : F (u-η) ∈ N := by
    apply hdN
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hwN : F (u+η) ∈ N := by
    apply hdN
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  obtain ⟨_,_,hsg⟩ := hsigns (u-η) (u+η) (by linarith) (by linarith) (by linarith) (by linarith)
  refine ⟨u-η,u+η,by linarith,by linarith,by linarith,by linarith,?_⟩
  rcases hsg with ⟨hl,hw⟩ | ⟨hl,hw⟩
  · apply local_connected_arms_opposite_sides L U V N A B (F u) (F (u-η)) (F (u+η))
      hU hV hdis hcover hN huN huU huV hsplit hA hB
    · rw [hAeq]; exact ⟨hlN,hl⟩
    · rw [hBeq]; exact ⟨hwN,hw⟩
  · have hh := local_connected_arms_opposite_sides L U V N A B (F u) (F (u+η)) (F (u-η))
      hU hV hdis hcover hN huN huU huV hsplit hA hB
      (by rw [hAeq]; exact ⟨hwN,hw⟩) (by rw [hBeq]; exact ⟨hlN,hl⟩)
    rcases hh with ⟨hwU,hlV⟩ | ⟨hwV,hlU⟩
    · exact Or.inr ⟨hlV,hwU⟩
    · exact Or.inl ⟨hlU,hwV⟩


private theorem actual_transverse_lift_switches_global_sides
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b) (F J : C(ℝ,H2)) (g : G)
    (hinj : Function.Injective F)
    (hF : ∀ t : ℝ, q (F t)=a.map (Circle.exp t))
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k : G) (u : ℝ) (hu : F u ∈ Set.range (fun t : ℝ => k • J t))
    (U V : Set H2) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V=(Set.range (fun t : ℝ => k • J t))ᶜ)
    (hfrontU : frontier U=Set.range (fun t : ℝ => k • J t))
    (hfrontV : frontier V=Set.range (fun t : ℝ => k • J t)) :
    ∀ r s : ℝ, r<u → u<s →
      ∃ l w : ℝ, r<l ∧ l<u ∧ u<w ∧ w<s ∧
        ((F l ∈ U ∧ F w ∈ V) ∨ (F l ∈ V ∧ F w ∈ U)) := by
  letI : T2Space X := isometric_quotient_cover_hausdorff q hq hdeck
  obtain ⟨W,hW,huW,hbranch⟩ := actual_target_lift_contact_local_branch q hq b J g hJ hperiod k (F u) hu
  have hua : q (F u) ∈ a.image := by rw [hF]; exact Set.mem_range_self _
  have hub : q (F u) ∈ b.image := (hbranch (F u) huW).mpr hu
  obtain ⟨K,huK,hzero,haxes⟩ := actual_cover_crossing_chart q
    hq.isCoveringMap.isLocalHomeomorph a b (F u) (ht.2 _ ⟨hua,hub⟩)
  let K' := K.restrOpen W hW
  have huK' : F u ∈ K'.source := ⟨huK,huW⟩
  apply actual_embedded_lift_crosses_global_sides F hinj
    (Set.range (fun t : ℝ => k • J t)) U V hU hV hdis hcover hfrontU hfrontV
    K' u huK'
  · change K (F u)=(0,0)
    exact hzero
  · intro t htK
    change (K (F t)).1=0
    apply (haxes (F t) htK.1).1.mp
    rw [hF]
    exact Set.mem_range_self _
  · intro x hxK
    change x ∈ Set.range (fun t : ℝ => k • J t) ↔ (K x).2=0
    exact (hbranch x hxK.2).symm.trans (haxes x hxK.1).2

end CurveComplex.Hyperbolic

open Set

private theorem periodic_contacts_force_return_from_finite_connector_bound
    {X I : Type} [DecidableEq I] (F : ℝ → X) (L : I → Set X) (σ : I → I)
    (i₀ : I) (u T : ℝ) (hT : 0 < T) (D : Finset I)
    (hcontact : ∀ n : ℕ, F (u+n*T) ∈ L (σ^[n] i₀))
    (hbound : ∀ N : ℕ, ∀ j : ℕ, j < N →
      σ^[j] i₀ ∈ D ∪ D.image (σ^[N])) :
    ∃ i r s, r < s ∧ F r ∈ L i ∧ F s ∈ L i := by
  classical
  by_contra h
  have huniq (i : I) (r s : ℝ) (hr : F r ∈ L i) (hs : F s ∈ L i) : r=s := by
    rcases lt_trichotomy r s with hrs | he | hsr
    · exact False.elim (h ⟨i,r,s,hrs,hr,hs⟩)
    · exact he
    · exact False.elim (h ⟨i,s,r,hsr,hs,hr⟩)
  let N := 2*D.card+1
  let A : Fin N → I := fun j => σ^[j.val] i₀
  have hinj : Function.Injective A := by
    intro j k he
    have hh := huniq (A j) (u+j.val*T) (u+k.val*T) (hcontact j.val)
      (by simpa only [A,he] using hcontact k.val)
    apply Fin.ext
    have hjk : (j.val : ℝ) = (k.val : ℝ) := by nlinarith
    exact_mod_cast hjk
  have hsub : Finset.univ.image A ⊆ D ∪ D.image (σ^[N]) := by
    intro i hi
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
    exact hbound N j.val j.isLt
  have hcard := Finset.card_le_card hsub
  have himage : (Finset.univ.image A).card = N := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  rw [himage] at hcard
  have hupper := Finset.card_union_le D (D.image (σ^[N]))
  have himageupper := Finset.card_image_le (s := D) (f := σ^[N])
  have hN : N = 2*D.card+1 := rfl
  omega

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem interval_separator_contact
    {X : Type} [TopologicalSpace X] (F : ℝ → X) (hF : Continuous F)
    (L U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (r s : ℝ) (hrs : r < s)
    (hr : F r ∈ U) (hs : F s ∈ V) :
    ∃ t ∈ Set.Ioo r s, F t ∈ L := by
  by_contra h
  have havoid : F '' Set.Icc r s ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hcover]
    intro hmem
    have htstrict : t ∈ Set.Ioo r s := by
      constructor
      · rcases eq_or_lt_of_le ht.1 with heq | hlt
        · subst t
          have : F r ∈ Lᶜ := by rw [←hcover]; exact Or.inl hr
          exact False.elim (this hmem)
        · exact hlt
      · rcases eq_or_lt_of_le ht.2 with heq | hlt
        · subst t
          have : F s ∈ Lᶜ := by rw [←hcover]; exact Or.inr hs
          exact False.elim (this hmem)
        · exact hlt
    exact h ⟨t,htstrict,hmem⟩
  have hconn := (isPreconnected_Icc (a := r) (b := s)).image F hF.continuousOn
  rcases hconn.subset_or_subset hU hV hdis havoid with hu | hv
  · exact Set.disjoint_left.mp hdis (hu ⟨s,⟨hrs.le,le_rfl⟩,rfl⟩) hs
  · exact Set.disjoint_left.mp hdis hr (hv ⟨r,⟨le_rfl,hrs.le⟩,rfl⟩)

private theorem crossing_inside_return_has_second_contact
    {X : Type} [TopologicalSpace X] (F : ℝ → X) (hF : Continuous F)
    (L U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (r s u : ℝ) (hru : r < u) (hus : u < s)
    (hr : F r ∈ U) (hs : F s ∈ U)
    (hcross : ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
      ((F l ∈ U ∧ F w ∈ V) ∨ (F l ∈ V ∧ F w ∈ U))) :
    ∃ v ∈ Set.Ioo r s, v ≠ u ∧ F v ∈ L := by
  obtain ⟨l,w,hrl,hlu,huw,hws,h⟩ := hcross
  rcases h with ⟨_,hw⟩ | ⟨hl,_⟩
  · obtain ⟨v,hv,hvL⟩ := interval_separator_contact F hF L V U hV hU
      hdis.symm (by rw [union_comm,hcover]) w s hws hw hs
    exact ⟨v,⟨hru.trans (huw.trans hv.1),hv.2⟩,ne_of_gt (huw.trans hv.1),hvL⟩
  · obtain ⟨v,hv,hvL⟩ := interval_separator_contact F hF L U V hU hV hdis
      hcover r l hrl hr hl
    exact ⟨v,⟨hv.1,hv.2.trans (hlu.trans hus)⟩,ne_of_lt (hv.2.trans hlu),hvL⟩

private theorem single_crossing_separates_endpoints
    {X : Type} [TopologicalSpace X] (F : ℝ → X) (hF : Continuous F)
    (L U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (r s u : ℝ) (hru : r < u) (hus : u < s)
    (hr : F r ∉ L) (hs : F s ∉ L)
    (hunique : ∀ t ∈ Set.Ioo r s, F t ∈ L → t=u)
    (hcross : ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
      ((F l ∈ U ∧ F w ∈ V) ∨ (F l ∈ V ∧ F w ∈ U))) :
    (F r ∈ U ∧ F s ∈ V) ∨ (F r ∈ V ∧ F s ∈ U) := by
  have hrside : F r ∈ U ∪ V := by rw [hcover]; exact hr
  have hsside : F s ∈ U ∪ V := by rw [hcover]; exact hs
  rcases hrside with hrU | hrV <;> rcases hsside with hsU | hsV
  · obtain ⟨t,ht,htu,htL⟩ := crossing_inside_return_has_second_contact
      F hF L U V hU hV hdis hcover r s u hru hus hrU hsU hcross
    exact False.elim (htu (hunique t ht htL))
  · exact Or.inl ⟨hrU,hsV⟩
  · exact Or.inr ⟨hrV,hsU⟩
  · have hc : ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
        ((F l ∈ V ∧ F w ∈ U) ∨ (F l ∈ U ∧ F w ∈ V)) := by
      obtain ⟨l,w,hrl,hlu,huw,hws,h⟩ := hcross
      exact ⟨l,w,hrl,hlu,huw,hws,h.symm⟩
    obtain ⟨t,ht,htu,htL⟩ := crossing_inside_return_has_second_contact
      F hF L V U hV hU hdis.symm (by rw [union_comm,hcover])
      r s u hru hus hrV hsV hc
    exact False.elim (htu (hunique t ht htL))

private theorem path_separator_contact
    {X : Type} [TopologicalSpace X] {a b : X}
    (p : Path a b) (L U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (ha : a ∈ U) (hb : b ∈ V) :
    (Set.range p ∩ L).Nonempty := by
  by_contra h
  have hsub : Set.range p ⊆ U ∪ V := by
    intro x hx
    rw [hcover]
    intro hxL
    exact h ⟨x,hx,hxL⟩
  rcases (isPreconnected_range p.continuous).subset_or_subset hU hV hdis hsub with hu | hv
  · have hbU : b ∈ U := hu ⟨1,p.target⟩
    exact Set.disjoint_left.mp hdis hbU hb
  · have haV : a ∈ V := hv ⟨0,p.source⟩
    exact Set.disjoint_left.mp hdis ha haV

private theorem separating_line_meets_reference_connectors
    {X : Type} [TopologicalSpace X] {a b y z : X}
    (p : Path a y) (q : Path b z) (L U V J : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V)
    (hcover : U ∪ V = Lᶜ) (hJ : IsPreconnected J)
    (hLJ : Disjoint L J) (hy : y ∈ J) (hz : z ∈ J)
    (hab : (a ∈ U ∧ b ∈ V) ∨ (a ∈ V ∧ b ∈ U)) :
    (Set.range p ∩ L).Nonempty ∨ (Set.range q ∩ L).Nonempty := by
  have hsub : J ⊆ U ∪ V := by
    intro x hx
    rw [hcover]
    exact fun hxL => Set.disjoint_left.mp hLJ hxL hx
  rcases hJ.subset_or_subset hU hV hdis hsub with hu | hv
  · rcases hab with ⟨_,hb⟩ | ⟨ha,_⟩
    · exact Or.inr (path_separator_contact q L V U hV hU hdis.symm
        (by rw [union_comm,hcover]) hb (hu hz))
    · exact Or.inl (path_separator_contact p L V U hV hU hdis.symm
        (by rw [union_comm,hcover]) ha (hu hy))
  · rcases hab with ⟨ha,_⟩ | ⟨_,hb⟩
    · exact Or.inl (path_separator_contact p L U V hU hV hdis hcover ha (hv hy))
    · exact Or.inr (path_separator_contact q L U V hU hV hdis hcover hb (hv hz))


private theorem periodic_separating_family_has_actual_return
    {X I : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (F : C(ℝ,X)) (g : X ≃ₜ X) (σ : I ≃ I) (L U V : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hdis : ∀ i, Disjoint (U i) (V i))
    (hcover : ∀ i, U i ∪ V i = (L i)ᶜ)
    (hlocal : LocallyFinite L)
    (hline : ∀ n : ℕ, ∀ i x, g^[n] x ∈ L (σ^[n] i) ↔ x ∈ L i)
    (J : Set X) (hJ : IsConnected J)
    (hJinv : ∀ x ∈ J, g x ∈ J)
    (hfamily : ∀ i, L i = J ∨ Disjoint (L i) J)
    (T : ℝ) (hT : 0 < T) (hperiod : ∀ t, F (t+T)=g (F t))
    (hcross : ∀ i u, F u ∈ L i → ∀ r s, r < u → u < s →
      ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
        ((F l ∈ U i ∧ F w ∈ V i) ∨ (F l ∈ V i ∧ F w ∈ U i)))
    (R u : ℝ) (i₀ : I) (hRu : R < u) (huR : u < R+T)
    (hR : ∀ i, F R ∉ L i) (hu : F u ∈ L i₀) :
    ∃ i r s, r < s ∧ F r ∈ L i ∧ F s ∈ L i := by
  classical
  by_contra hnoreturn
  have huniq (i : I) (r s : ℝ) (hr : F r ∈ L i) (hs : F s ∈ L i) : r=s := by
    rcases lt_trichotomy r s with hrs | he | hsr
    · exact False.elim (hnoreturn ⟨i,r,s,hrs,hr,hs⟩)
    · exact he
    · exact False.elim (hnoreturn ⟨i,s,r,hsr,hs,hr⟩)
  have hiter (n : ℕ) (t : ℝ) : F (t+n*T)=g^[n] (F t) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have he : t+(n+1:ℕ)*T=(t+n*T)+T := by push_cast; ring
      rw [he,hperiod,ih,Function.iterate_succ_apply']
  obtain ⟨y,hy⟩ := hJ.nonempty
  let p : Path (F R) y := (PathConnectedSpace.joined (F R) y).somePath
  have hpcompact : IsCompact (Set.range p) := isCompact_range p.continuous
  let D : Finset I := (hlocal.finite_nonempty_inter_compact hpcompact).toFinset
  have hD (i : I) : i ∈ D ↔ (L i ∩ Set.range p).Nonempty := Set.Finite.mem_toFinset _
  have hcontact (n : ℕ) : F (u+n*T) ∈ L (σ^[n] i₀) := by
    rw [hiter]
    exact (hline n i₀ (F u)).mpr hu
  have hbound (N j : ℕ) (hj : j<N) : σ^[j] i₀ ∈ D ∪ D.image (σ^[N]) := by
    let i := σ^[j] i₀
    let t := u+j*T
    have hit : F t ∈ L i := hcontact j
    have htleft : R<t := by dsimp [t]; nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ))]
    have htright : t<R+N*T := by
      have hj' : (j:ℝ)+1≤(N:ℝ) := by exact_mod_cast hj
      dsimp [t]
      nlinarith
    have hlast : F (R+N*T) ∉ L i := by
      obtain ⟨i',hi'⟩ := σ.surjective.iterate N i
      rw [hiter,←hi',hline]
      exact hR i'
    have hsep := single_crossing_separates_endpoints F F.continuous (L i) (U i) (V i)
      (hU i) (hV i) (hdis i) (hcover i) R (R+N*T) t htleft htright
      (hR i) hlast (fun v _ hv => huniq i v t hv hit)
      (hcross i t hit R (R+N*T) htleft htright)
    have hLiJ : Disjoint (L i) J := by
      rcases hfamily i with he | hd
      · have hnext : F (t+T) ∈ L i := by rw [he,hperiod]; exact hJinv _ (he ▸ hit)
        have hh := huniq i t (t+T) hit hnext
        linarith
      · exact hd
    have hgnJ : ∀ n : ℕ, g^[n] y ∈ J := by
      intro n
      induction n with
      | zero => simpa using hy
      | succ n ih => rw [Function.iterate_succ_apply']; exact hJinv _ ih
    let pn : Path (F (R+N*T)) (g^[N] y) :=
      (p.map (g.continuous.iterate N)).cast (hiter N R) rfl
    have hmeet := separating_line_meets_reference_connectors p pn (L i) (U i) (V i) J
      (hU i) (hV i) (hdis i) (hcover i) hJ.isPreconnected hLiJ hy (hgnJ N) hsep
    rcases hmeet with hp | hpn
    · exact Finset.mem_union.mpr (Or.inl ((hD i).mpr (hp.mono (by intro x hx; exact ⟨hx.2,hx.1⟩))))
    · obtain ⟨x,⟨v,hv⟩,hxL⟩ := hpn
      obtain ⟨i',hi'⟩ := σ.surjective.iterate N i
      have hvL : p v ∈ L i' := by
        apply (hline N i' (p v)).mp
        rw [hi']
        change g^[N] (p v)=x at hv
        rwa [hv]
      apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨i',(hD i').mpr ⟨p v,hvL,⟨v,rfl⟩⟩,hi'⟩
  exact hnoreturn (periodic_contacts_force_return_from_finite_connector_bound
    F L σ i₀ u T hT D hcontact hbound)

/-- A genuine return among disjoint separating target lifts has a clean
minimal return. Local crossings, finite actual contacts, and separation are
geometric inputs; clean contacts are constructed rather than supplied. -/
private theorem separating_family_minimal_return_clean
    {X I : Type} [TopologicalSpace X]
    (F : ℝ → X) (hF : Continuous F) (L U V : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hdis : ∀ i, Disjoint (U i) (V i))
    (hcover : ∀ i, U i ∪ V i = (L i)ᶜ)
    (hconn : ∀ i, IsPreconnected (L i))
    (hpair : Pairwise fun i j => Disjoint (L i) (L j))
    (hcross : ∀ i u, F u ∈ L i → ∀ r s, r < u → u < s →
      ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
        ((F l ∈ U i ∧ F w ∈ V i) ∨ (F l ∈ V i ∧ F w ∈ U i)))
    (R T : ℝ)
    (hfinite : {t | t ∈ Set.Icc R T ∧ ∃ i, F t ∈ L i}.Finite)
    (i₀ : I) (r₀ s₀ : ℝ) (hR : R ≤ r₀) (hT : s₀ ≤ T) (h₀ : r₀ < s₀)
    (hr₀ : F r₀ ∈ L i₀) (hs₀ : F s₀ ∈ L i₀) :
    ∃ i r s, R ≤ r ∧ s ≤ T ∧ r < s ∧ s-r ≤ s₀-r₀ ∧
      F r ∈ L i ∧ F s ∈ L i ∧
      ∀ t ∈ Set.Ioo r s, ∀ j, F t ∉ L j := by
  classical
  let S : Set ℝ := {t | t ∈ Set.Icc R T ∧ ∃ i, F t ∈ L i}
  let D : Set ℝ := {d | ∃ i r s, r ∈ S ∧ s ∈ S ∧ r < s ∧
    F r ∈ L i ∧ F s ∈ L i ∧ d=s-r}
  have hDfinite : D.Finite := by
    apply ((hfinite.prod hfinite).image (fun p : ℝ × ℝ => p.2-p.1)).subset
    rintro d ⟨i,r,s,hr,hs,hrs,_,_,rfl⟩
    exact ⟨(r,s),⟨hr,hs⟩,rfl⟩
  have hD₀ : s₀-r₀ ∈ D := by
    exact ⟨i₀,r₀,s₀,⟨⟨hR,h₀.le.trans hT⟩,i₀,hr₀⟩,
      ⟨⟨hR.trans h₀.le,hT⟩,i₀,hs₀⟩,h₀,hr₀,hs₀,rfl⟩
  have hleast := (show D.Nonempty from ⟨_,hD₀⟩).isLeast_csInf hDfinite
  obtain ⟨i,r,s,hr,hs,hrs,hri,hsi,he⟩ := hleast.1
  have hmin (d : ℝ) (hd : d ∈ D) : s-r ≤ d := by rw [←he]; exact hleast.2 hd
  refine ⟨i,r,s,hr.1.1,hs.1.2,hrs,hmin _ hD₀,hri,hsi,?_⟩
  intro u hu j huj
  have huS : u ∈ S := ⟨⟨hr.1.1.trans hu.1.le,hu.2.le.trans hs.1.2⟩,j,huj⟩
  by_cases hij : i=j
  · subst j
    have hd : u-r ∈ D := ⟨i,r,u,hr,huS,hu.1,hri,huj,rfl⟩
    have hh := hmin _ hd
    linarith [hu.2]
  · have hLi : L i ⊆ U j ∪ V j := by
      intro x hx
      rw [hcover j]
      exact fun hxj => Set.disjoint_left.mp (hpair hij) hx hxj
    rcases (hconn i).subset_or_subset (hU j) (hV j) (hdis j) hLi with hside | hside
    all_goals
      have hlocal := hcross j u huj r s hu.1 hu.2
    · obtain ⟨v,hv,hvu,hvj⟩ := crossing_inside_return_has_second_contact
        F hF (L j) (U j) (V j) (hU j) (hV j) (hdis j) (hcover j)
        r s u hu.1 hu.2 (hside hri) (hside hsi) hlocal
      have hvS : v ∈ S := ⟨⟨hr.1.1.trans hv.1.le,hv.2.le.trans hs.1.2⟩,j,hvj⟩
      rcases lt_or_gt_of_ne hvu with hvu | huv
      · have hd : u-v ∈ D := ⟨j,v,u,hvS,huS,hvu,hvj,huj,rfl⟩
        have hh := hmin _ hd
        linarith [hv.1,hu.2]
      · have hd : v-u ∈ D := ⟨j,u,v,huS,hvS,huv,huj,hvj,rfl⟩
        have hh := hmin _ hd
        linarith [hu.1,hv.2]
    · have hlocal' : ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
          ((F l ∈ V j ∧ F w ∈ U j) ∨ (F l ∈ U j ∧ F w ∈ V j)) := by
        obtain ⟨l,w,h1,h2,h3,h4,h5⟩ := hlocal
        exact ⟨l,w,h1,h2,h3,h4,h5.symm⟩
      obtain ⟨v,hv,hvu,hvj⟩ := crossing_inside_return_has_second_contact
        F hF (L j) (V j) (U j) (hV j) (hU j) (hdis j).symm
        (by rw [union_comm,hcover j]) r s u hu.1 hu.2
        (hside hri) (hside hsi) hlocal'
      have hvS : v ∈ S := ⟨⟨hr.1.1.trans hv.1.le,hv.2.le.trans hs.1.2⟩,j,hvj⟩
      rcases lt_or_gt_of_ne hvu with hvu | huv
      · have hd : u-v ∈ D := ⟨j,v,u,hvS,huS,hvu,hvj,huj,rfl⟩
        have hh := hmin _ hd
        linarith [hv.1,hu.2]
      · have hd : v-u ∈ D := ⟨j,u,v,huS,hvS,huv,huj,hvj,rfl⟩
        have hh := hmin _ hd
        linarith [hu.1,hv.2]

private theorem finite_actual_curve_contact_parameters
    {X : Type} [TopologicalSpace X] (a b : Curve X)
    (hfinite : (a.image ∩ b.image).Finite) (R T : ℝ) :
    {t | t ∈ Set.Icc R T ∧ a.map (Circle.exp t) ∈ b.image}.Finite := by
  classical
  let W : ℝ → Set ℝ := fun x => Set.Ioo (x-Real.pi/2) (x+Real.pi/2)
  have hlocal (x : ℝ) : {t | t ∈ W x ∧ a.map (Circle.exp t) ∈ b.image}.Finite := by
    apply Set.Finite.of_injOn (f := fun t : ℝ => a.map (Circle.exp t))
      (t := a.image ∩ b.image) _ _ hfinite
    · intro t ht
      exact ⟨Set.mem_range_self _,ht.2⟩
    · intro t ht u hu he
      have hwidth : (x+Real.pi/2)-(x-Real.pi/2) < 2*Real.pi := by linarith [Real.pi_pos]
      exact Circle.exp_injOn_Icc hwidth ⟨ht.1.1.le,ht.1.2.le⟩
        ⟨hu.1.1.le,hu.1.2.le⟩ (a.embedded.injective he)
  obtain ⟨K,hK⟩ := (isCompact_Icc (a := R) (b := T)).elim_finite_subcover W
    (fun _ => isOpen_Ioo) (by
      intro t ht
      exact Set.mem_iUnion.mpr ⟨t,by dsimp [W]; constructor <;> linarith [Real.pi_pos]⟩)
  have hbig : (⋃ x ∈ (K : Set ℝ), {t | t ∈ W x ∧ a.map (Circle.exp t) ∈ b.image}).Finite :=
    K.finite_toSet.biUnion fun x _ => hlocal x
  apply hbig.subset
  intro t ht
  obtain ⟨x,hx,hxt⟩ := Set.mem_iUnion₂.mp (hK ht.1)
  exact Set.mem_iUnion₂.mpr ⟨x,hx,hxt,ht.2⟩

private theorem local_injective_coordinate_crosses_arms
    {X : Type} (F : ℝ → X) (A B : Set X) (φ : ℝ → ℝ)
    (a b u : ℝ) (hau : a < u) (hub : u < b)
    (hφ : ContinuousOn φ (Set.Icc a b)) (hinj : Set.InjOn φ (Set.Icc a b))
    (hzero : φ u = 0)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < φ t → F t ∈ A)
    (hneg : ∀ t ∈ Set.Icc a b, φ t < 0 → F t ∈ B) :
    ∀ r s, r < u → u < s →
      ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
        ((F l ∈ A ∧ F w ∈ B) ∨ (F l ∈ B ∧ F w ∈ A)) := by
  intro r s hru hus
  obtain ⟨l,hllow,hlu⟩ := exists_between (max_lt hau hru)
  obtain ⟨w,huw,hwhigh⟩ := exists_between (lt_min hub hus)
  have hl : l ∈ Set.Icc a b :=
    ⟨(le_max_left a r).trans hllow.le,hlu.le.trans hub.le⟩
  have hw : w ∈ Set.Icc a b :=
    ⟨hau.le.trans huw.le,hwhigh.le.trans (min_le_left b s)⟩
  have hu : u ∈ Set.Icc a b := ⟨hau.le,hub.le⟩
  refine ⟨l,w,(le_max_right a r).trans_lt hllow,hlu,huw,
    hwhigh.trans_le (min_le_right b s),?_⟩
  rcases ContinuousOn.strictMonoOn_of_injOn_Icc' (hau.le.trans hub.le) hφ hinj with hmono | hanti
  · have hφl : φ l < 0 := by simpa [hzero] using hmono hl hu hlu
    have hφw : 0 < φ w := by simpa [hzero] using hmono hu hw huw
    exact Or.inr ⟨hneg l hl hφl,hpos w hw hφw⟩
  · have hφl : 0 < φ l := by simpa [hzero] using hanti hl hu hlu
    have hφw : φ w < 0 := by simpa [hzero] using hanti hu hw huw
    exact Or.inl ⟨hpos l hl hφl,hneg w hw hφw⟩

private theorem clean_actual_curve_interval_short
    {X : Type} [TopologicalSpace X] (a b : Curve X)
    (hfinite : (a.image ∩ b.image).Finite)
    (hcount : 2 ≤ (a.image ∩ b.image).ncard)
    (r s : ℝ) (hclean : ∀ t ∈ Set.Ioo r s, a.map (Circle.exp t) ∉ b.image) :
    s-r < 2*Real.pi := by
  obtain ⟨x,hx,y,hy,hxy⟩ := (Set.one_lt_ncard hfinite).mp (by omega)
  obtain ⟨z,hz,hzne⟩ : ∃ z ∈ a.image ∩ b.image, z ≠ a.map (Circle.exp r) := by
    by_cases heq : x=a.map (Circle.exp r)
    · exact ⟨y,hy,by intro h; apply hxy; exact heq.trans h.symm⟩
    · exact ⟨x,hx,heq⟩
  obtain ⟨w,hw⟩ := hz.1
  have hwne : Circle.exp r ≠ w := by
    intro h
    apply hzne
    rw [←hw,←h]
  let t := r+Circle.angleDiff (Circle.exp r) w
  have htw : Circle.exp t=w := by
    dsimp [t]
    rw [Circle.exp_add,mul_comm,Circle.exp_angleDiff_mul]
  have htr : r < t := by
    have := Circle.angleDiff_pos hwne
    dsimp [t]
    linarith
  have httop : t < r+2*Real.pi := by
    have := Circle.angleDiff_lt_two_pi (x := Circle.exp r) (y := w)
    dsimp [t]
    linarith
  by_contra hwidth
  have hts : t < s := httop.trans_le (by linarith [le_of_not_gt hwidth])
  apply hclean t ⟨htr,hts⟩
  rw [htw,hw]
  exact hz.2


private theorem periodic_separating_family_has_clean_return
    {X I : Type} [TopologicalSpace X] [PathConnectedSpace X]
    (F : C(ℝ,X)) (g : X ≃ₜ X) (σ : I ≃ I) (L U V : I → Set X)
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i))
    (hdis : ∀ i, Disjoint (U i) (V i))
    (hcover : ∀ i, U i ∪ V i = (L i)ᶜ)
    (hlocal : LocallyFinite L)
    (hconn : ∀ i, IsPreconnected (L i))
    (hpair : Pairwise fun i j => Disjoint (L i) (L j))
    (hfinite : ∀ r s : ℝ, {t | t ∈ Set.Icc r s ∧ ∃ i, F t ∈ L i}.Finite)
    (hline : ∀ n : ℕ, ∀ i x, g^[n] x ∈ L (σ^[n] i) ↔ x ∈ L i)
    (J : Set X) (hJ : IsConnected J)
    (hJinv : ∀ x ∈ J, g x ∈ J)
    (hfamily : ∀ i, L i = J ∨ Disjoint (L i) J)
    (T : ℝ) (hT : 0 < T) (hperiod : ∀ t, F (t+T)=g (F t))
    (hcross : ∀ i u, F u ∈ L i → ∀ r s, r < u → u < s →
      ∃ l w : ℝ, r < l ∧ l < u ∧ u < w ∧ w < s ∧
        ((F l ∈ U i ∧ F w ∈ V i) ∨ (F l ∈ V i ∧ F w ∈ U i)))
    (R u : ℝ) (i₀ : I) (hRu : R < u) (huR : u < R+T)
    (hR : ∀ i, F R ∉ L i) (hu : F u ∈ L i₀) :
    ∃ i r s, r < s ∧ F r ∈ L i ∧ F s ∈ L i ∧
      ∀ t ∈ Set.Ioo r s, ∀ j, F t ∉ L j := by
  obtain ⟨i₀',r₀,s₀,hrs,hr,hs⟩ := periodic_separating_family_has_actual_return
    F g σ L U V hU hV hdis hcover hlocal hline J hJ hJinv hfamily
    T hT hperiod hcross R u i₀ hRu huR hR hu
  obtain ⟨i,r,s,_,_,hrs',_,hr',hs',hclean⟩ := separating_family_minimal_return_clean
    F F.continuous L U V hU hV hdis hcover hconn hpair hcross r₀ s₀
    (hfinite r₀ s₀) i₀' r₀ s₀ le_rfl le_rfl hrs hr hs
  exact ⟨i,r,s,hrs',hr',hs',hclean⟩

private theorem actual_curve_contact_has_off_contact_basepoint
    {X : Type} [TopologicalSpace X] (a b : Curve X)
    (hfinite : (a.image ∩ b.image).Finite) (u : ℝ) :
    ∃ R : ℝ, R<u ∧ u<R+2*Real.pi ∧ a.map (Circle.exp R) ∉ b.image := by
  let S : Set ℝ := {t | t ∈ Set.Icc (u-2*Real.pi) u ∧ a.map (Circle.exp t) ∈ b.image}
  have hS : S.Finite := finite_actual_curve_contact_parameters a b hfinite (u-2*Real.pi) u
  have hinf : (Set.Ioo (u-2*Real.pi) u).Infinite := Set.Ioo_infinite (by linarith [Real.pi_pos])
  obtain ⟨R,hR,hRS⟩ := (hinf.sdiff hS).nonempty
  refine ⟨R,hR.2,by linarith [hR.1],?_⟩
  intro hRb
  exact hRS ⟨⟨hR.1.le,hR.2.le⟩,hRb⟩

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology

-- The local properness block is mechanically reused from G3OriginalConstruction.
private theorem actual_uniform_displacement_periodic_lift_closed_embedding
    {E G : Type} [TopologicalSpace E] [Group G] [MulAction G H2]
    (q : H2 → E) (c : Curve E) (F : C(ℝ,H2)) (g : G)
    (hg : Isometry (fun z : H2 => g • z)) (ε : ℝ) (hε : 0 < ε)
    (hdisp : ∀ z : H2, ε ≤ dist z (g • z))
    (hproj : ∀ s : ℝ, q (F s)=c.map (Circle.exp s))
    (hperiod : ∀ s : ℝ, F (s+2*Real.pi)=g • F s) :
    IsProperMap F ∧ IsClosedEmbedding F := by
  have actual_axis_orbit_escape
      {X : Type} [MetricSpace X] (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ)
      (hτ : 0 < τ) (htranslate : ∀ t, g (axis t) = axis (t + τ)) :
      (∀ n : ℕ, ∀ t : ℝ, g^[n] (axis t) = axis (t + n * τ)) ∧
      (∀ x : X, ∀ n : ℕ,
        n * τ ≤ dist x (g^[n] x) + 2 * dist x (axis 0)) ∧
      (∀ x : X, ∀ m : ℕ, 0 < m → g^[m] x ≠ x) := by
    have hiter (n : ℕ) (t : ℝ) : g^[n] (axis t) = axis (t + n * τ) := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', ih, htranslate]
        congr 1
        push_cast
        ring
    have hidist (n : ℕ) (x y : X) : dist (g^[n] x) (g^[n] y) = dist x y := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Function.iterate_succ_apply', hg.dist_eq] using ih
    have hbound (x : X) (n : ℕ) :
        n * τ ≤ dist x (g^[n] x) + 2 * dist x (axis 0) := by
      have hn : 0 ≤ (n : ℝ) * τ := mul_nonneg (Nat.cast_nonneg n) hτ.le
      have haxisdist : dist (axis 0) (g^[n] (axis 0)) = n * τ := by
        rw [hiter, zero_add, haxis.dist_eq, Real.dist_eq, zero_sub, abs_neg,
          abs_of_nonneg hn]
      have htriangle := dist_triangle (axis 0) x (g^[n] (axis 0))
      have htriangle' := dist_triangle x (g^[n] x) (g^[n] (axis 0))
      rw [hidist] at htriangle'
      rw [haxisdist, dist_comm (axis 0) x] at htriangle
      linarith
    refine ⟨hiter, hbound, ?_⟩
    intro x m hm hfix
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
    obtain ⟨k, hk⟩ := exists_nat_gt (2 * dist x (axis 0) / ((m : ℝ) * τ))
    have hlarge := (div_lt_iff₀ (mul_pos hmreal hτ)).mp hk
    have hfix' : g^[m * k] x = x := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hfix k
    have hsmall := hbound x (m * k)
    rw [hfix', dist_self, zero_add, Nat.cast_mul] at hsmall
    nlinarith
  have actual_axis_periodic_curve_lift_injective
      {X : Type} [MetricSpace X] (p : X → E) (c : Curve E)
      (F : ℝ → X) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hproj : ∀ s, p (F s) = c.map (Circle.exp s))
      (hperiod : ∀ s, F (s + 2 * Real.pi) = g (F s)) :
      Function.Injective F := by
    have hno := (actual_axis_orbit_escape g hg axis haxis τ hτ htranslate).2.2
    have hiter (n : ℕ) (s : ℝ) : F (s + n * (2 * Real.pi)) = g^[n] (F s) := by
      induction n with
      | zero => simp
      | succ n ih =>
        have he : s + (n + 1 : ℕ) * (2 * Real.pi) =
            (s + n * (2 * Real.pi)) + 2 * Real.pi := by push_cast; ring
        rw [he, hperiod, ih, Function.iterate_succ_apply']
    intro s t hst
    have he : Circle.exp s = Circle.exp t := by
      apply c.embedded.injective
      rw [← hproj, ← hproj, hst]
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp he
    cases k with
    | ofNat n =>
      change s = t + (n : ℝ) * (2 * Real.pi) at hk
      by_cases hn : n = 0
      · simpa [hn] using hk
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hfix : g^[n] (F t) = F t := by
          rw [← hiter, ← hk]
          exact hst
        exact False.elim (hno (F t) n hnpos hfix)
    | negSucc n =>
      have ht : t = s + (n + 1 : ℕ) * (2 * Real.pi) := by
        simp only [Int.cast_negSucc] at hk
        push_cast at hk
        push_cast
        linarith
      have hfix : g^[n + 1] (F s) = F s := by
        rw [← hiter, ← ht]
        exact hst.symm
      exact False.elim (hno (F s) (n + 1) (Nat.succ_pos _) hfix)
  have actual_axis_periodic_line_proper
      {X : Type} [MetricSpace X] (F : C(ℝ,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ T : ℝ) (hτ : 0 < τ) (hT : 0 < T)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hperiod : ∀ s, F (s + T) = g (F s)) :
      IsProperMap F := by
    let δ : ℝ → ℝ := fun s => dist (F s) (axis (s * (τ / T)))
    have hδcont : Continuous δ := F.continuous.dist (haxis.continuous.comp
      (continuous_id.mul continuous_const))
    have hδperiod : Function.Periodic δ T := by
      intro s
      dsimp [δ]
      have he : (s + T) * (τ / T) = s * (τ / T) + τ := by
        field_simp
      rw [hperiod, he, ← htranslate, hg.dist_eq]
    have hcompact : IsCompact (Set.range δ) := by
      rw [← hδperiod.image_Icc hT 0]
      exact isCompact_Icc.image hδcont
    obtain ⟨M,hM⟩ := hcompact.bddAbove
    have hbound (s : ℝ) : δ s ≤ M := hM ⟨s,rfl⟩
    have hlower (s : ℝ) : |s| * (τ / T) - M ≤ dist (F s) (axis 0) := by
      have htri := dist_triangle (axis (s * (τ / T))) (F s) (axis 0)
      rw [haxis.dist_eq, Real.dist_eq, sub_zero, abs_mul,
        abs_of_pos (div_pos hτ hT), dist_comm (axis (s * (τ / T))) (F s)] at htri
      have hb := hbound s
      dsimp [δ] at hb
      linarith
    have habs : Filter.Tendsto (fun s : ℝ => |s|) (Filter.cocompact ℝ) Filter.atTop := by
      convert tendsto_dist_right_cocompact_atTop (0 : ℝ) using 1
      ext s
      simp [Real.dist_eq]
    have hdist : Filter.Tendsto (fun s : ℝ => dist (F s) (axis 0))
        (Filter.cocompact ℝ) Filter.atTop := by
      apply Filter.tendsto_atTop.mpr
      intro R
      filter_upwards [(Filter.tendsto_atTop.mp habs) ((R + M) / (τ / T))] with s hs
      have hh := (div_le_iff₀ (div_pos hτ hT)).mp hs
      have hl := hlower s
      linarith
    exact isProperMap_iff_tendsto_cocompact.mpr
      ⟨F.continuous,tendsto_cocompact_of_tendsto_dist_comp_atTop (axis 0) hdist⟩
  have actual_axis_periodic_curve_lift_closed_embedding
      {X : Type} [MetricSpace X] (p : X → E) (c : Curve E)
      (F : C(ℝ,X)) (g : X → X) (hg : Isometry g)
      (axis : ℝ → X) (haxis : Isometry axis) (τ : ℝ) (hτ : 0 < τ)
      (htranslate : ∀ t, g (axis t) = axis (t + τ))
      (hproj : ∀ s, p (F s) = c.map (Circle.exp s))
      (hperiod : ∀ s, F (s + 2 * Real.pi) = g (F s)) :
      IsClosedEmbedding F := by
    have hproper := actual_axis_periodic_line_proper F g hg axis haxis
      τ (2 * Real.pi) hτ (by positivity) htranslate hperiod
    have hinj := actual_axis_periodic_curve_lift_injective p c F g hg axis haxis
      τ hτ htranslate hproj hperiod
    exact Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap
      F.continuous hinj hproper.isClosedMap

  let γ : H2 ≃ᵢ H2 :=
    { toEquiv :=
        { toFun := fun z => g • z
          invFun := fun z => g⁻¹ • z
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
      isometry_toFun := hg }
  obtain ⟨axis,haxis,τ,hτ,htranslate⟩ :=
    actual_hyperbolic_isometry_axis_of_uniform_displacement γ ε hε hdisp
  exact ⟨actual_axis_periodic_line_proper F γ hg axis haxis τ (2*Real.pi)
      hτ (by positivity) htranslate hperiod,
    actual_axis_periodic_curve_lift_closed_embedding q c F γ hg axis haxis τ hτ
      htranslate hproj hperiod⟩

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem actual_h2_proper_line_separates
    (F : C(ℝ,H2)) (hproper : IsProperMap F) (hinj : Function.Injective F)
    (a : H2) (ha : a ∉ Set.range F) :
    ∃ U V : Set H2, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (Set.range F)ᶜ ∧
      frontier U = Set.range F ∧ frontier V = Set.range F := by
  let e := hyperbolicPlaneHomeomorph
  let P : C(ℝ,Schoenflies.Plane) := ⟨e ∘ F,e.continuous.comp F.continuous⟩
  have hPr : Set.range P = e '' Set.range F := Set.range_comp e F
  have haP : e a ∉ Set.range P := by
    rw [hPr]
    rintro ⟨x,hx,he⟩
    exact ha (e.injective he ▸ hx)
  have hJ := CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.proper_line_inversion_isJordanCurve
    P (e.isProperMap.comp hproper) (e.injective.comp hinj) (e a) haP
  obtain ⟨U,V,hU,hV,hUc,hVc,hdis,hcover,hfrontU,hfrontV⟩ :=
    CurveComplexGenusTwo.Topology.PuncturedTorusCandidate.proper_line_sides_of_inversion_jordan
      (Set.range P) (e a) haP hJ
  have hpre : e ⁻¹' Set.range P = Set.range F := by
    rw [hPr,Set.preimage_image_eq _ e.injective]
  refine ⟨e ⁻¹' U,e ⁻¹' V,hU.preimage e.continuous,hV.preimage e.continuous,
    e.isConnected_preimage.mpr hUc,e.isConnected_preimage.mpr hVc,
    hdis.preimage e,?_,?_,?_⟩
  · rw [←Set.preimage_union,hcover,Set.preimage_compl,hpre]
  · rw [←e.preimage_frontier,hfrontU,hpre]
  · rw [←e.preimage_frontier,hfrontV,hpre]

end CurveComplex.Hyperbolic

open Set

private theorem actual_deck_image_lift_range
    {P G : Type} [Group G] [MulAction G P]
    (J : ℝ → P) (g k : G) :
    (fun z : P => g • z) '' Set.range (fun t : ℝ => k • J t) =
      Set.range (fun t : ℝ => (g*k) • J t) := by
  rw [←Set.range_comp]
  congr 1
  funext t
  exact (mul_smul g k (J t)).symm

private theorem actual_lift_family_deck_permutation
    {P G : Type} [Group G] [MulAction G P]
    (J : ℝ → P) (g : G) :
    ∃ σ : Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)) ≃
        Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)),
      ∀ L, (σ L : Set P) = (fun z : P => g • z) '' (L : Set P) := by
  let R : G → Set P := fun k => Set.range (fun t : ℝ => k • J t)
  have hclosed (m : G) (L : Set.range R) :
      (fun z : P => m • z) '' (L : Set P) ∈ Set.range R := by
    obtain ⟨k,hk⟩ := L.2
    rw [←hk,actual_deck_image_lift_range]
    exact ⟨m*k,rfl⟩
  let f : Set.range R → Set.range R := fun L => ⟨_,hclosed g L⟩
  let h : Set.range R → Set.range R := fun L => ⟨_,hclosed g⁻¹ L⟩
  have hleft : Function.LeftInverse h f := by
    intro L
    apply Subtype.ext
    change (fun z : P => g⁻¹ • z) '' ((fun z : P => g • z) '' (L : Set P)) = _
    rw [Set.image_image]
    simpa only [Function.comp_def,smul_smul,inv_mul_cancel,one_smul,Set.image_id']
  have hright : Function.RightInverse h f := by
    intro L
    apply Subtype.ext
    change (fun z : P => g • z) '' ((fun z : P => g⁻¹ • z) '' (L : Set P)) = _
    rw [Set.image_image]
    simpa only [Function.comp_def,smul_smul,mul_inv_cancel,one_smul,Set.image_id']
  exact ⟨⟨f,h,hleft,hright⟩,fun _ => rfl⟩

private theorem actual_lift_family_deck_permutation_iterates
    {P G : Type} [Group G] [MulAction G P]
    (J : ℝ → P) (g : G)
    (σ : Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)) ≃
      Set.range (fun k : G => Set.range (fun t : ℝ => k • J t)))
    (hσ : ∀ L, (σ L : Set P) = (fun z : P => g • z) '' (L : Set P)) :
    ∀ n : ℕ, ∀ L x,
      (fun z : P => g • z)^[n] x ∈ (σ^[n] L : Set P) ↔ x ∈ (L : Set P) := by
  intro n
  induction n with
  | zero => intro L x; rfl
  | succ n ih =>
    intro L x
    rw [Function.iterate_succ_apply',Function.iterate_succ_apply',hσ]
    constructor
    · rintro ⟨z,hz,he⟩
      have hz' : z=(fun w : P => g • w)^[n] x := by
        exact (MulAction.injective g) he
      rw [hz'] at hz
      exact (ih L x).mp hz
    · intro hx
      exact ⟨_,(ih L x).mpr hx,rfl⟩
namespace CurveComplex.Hyperbolic
open Set Topology

private theorem actual_periodic_h2_clean_same_lift_return
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b) (hcount : 2≤(a.image ∩ b.image).ncard)
    (F J : C(ℝ,H2)) (g : G) (ε : ℝ) (hε : 0<ε)
    (hdisp : ∀ z : H2, ε≤dist z (g • z))
    (hF : ∀ t : ℝ, q (F t)=a.map (Circle.exp t))
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hFperiod : ∀ t : ℝ, F (t+2*Real.pi)=g • F t)
    (hJperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t) :
    ∃ r s t v : ℝ, r<s ∧ s-r<2*Real.pi ∧ t≠v ∧ ∃ k : G,
      F r=k • J t ∧ F s=k • J v ∧
      ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image := by
  classical
  letI : T2Space X := isometric_quotient_cover_hausdorff q hq hdeck
  have hFp := actual_uniform_displacement_periodic_lift_closed_embedding q a F g
    (hdeck g) ε hε hdisp hF hFperiod
  have hJp := actual_uniform_displacement_periodic_lift_closed_embedding q b J g
    (hdeck g) ε hε hdisp hJ hJperiod
  let Ranges : G → Set H2 := fun k => Set.range (fun t : ℝ => k • J t)
  let I := Set.range Ranges
  let L : I → Set H2 := Subtype.val
  obtain ⟨σ,hσ⟩ := actual_lift_family_deck_permutation J g
  let deckHomeo (k : G) : H2 ≃ₜ H2 :=
    { toEquiv :=
        { toFun := fun z => k • z
          invFun := fun z => k⁻¹ • z
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
      continuous_toFun := (hdeck k).continuous
      continuous_invFun := (hdeck k⁻¹).continuous }
  let η := deckHomeo g
  have hcontacts (t : ℝ) : (∃ i : I, F t ∈ L i) ↔ q (F t) ∈ b.image := by
    have hc : q (F t) ∈ b.image ↔ ∃ k : G, ∃ v : ℝ, F t=k • J v :=
      actual_target_lift_family_contacts q hq id Function.injective_id b J hJ (F t)
    rw [hc]
    constructor
    · rintro ⟨i,hi⟩
      obtain ⟨k,hk⟩ := i.2
      change Ranges k=L i at hk
      have hi' : F t ∈ Ranges k := hk.symm ▸ hi
      obtain ⟨v,hv⟩ := hi'
      exact ⟨k,v,hv.symm⟩
    · rintro ⟨k,v,hv⟩
      exact ⟨⟨Ranges k,⟨k,rfl⟩⟩,v,hv.symm⟩
  obtain ⟨z,hz,w,hw,hzw⟩ := (Set.one_lt_ncard ht.1).mp (by omega : 1<(a.image ∩ b.image).ncard)
  obtain ⟨c,hc⟩ := hz.1
  obtain ⟨u,hu⟩ := Circle.exp_surjective c
  have huB : q (F u) ∈ b.image := by rw [hF,hu,hc]; exact hz.2
  obtain ⟨i₀,hi₀⟩ := (hcontacts u).mpr huB
  obtain ⟨R,hRu,huR,hRb⟩ := actual_curve_contact_has_off_contact_basepoint a b ht.1 u
  have hR : ∀ i : I, F R ∉ L i := by
    intro i hi
    exact hRb (by rw [←hF]; exact (hcontacts R).mp ⟨i,hi⟩)
  have hsides (i : I) : ∃ U V : Set H2,
      IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧ Disjoint U V ∧
      U ∪ V=(L i)ᶜ ∧ frontier U=L i ∧ frontier V=L i := by
    obtain ⟨k,hk⟩ := i.2
    change Ranges k=L i at hk
    let Jk : C(ℝ,H2) := ⟨fun t => k • J t,(hdeck k).continuous.comp J.continuous⟩
    have hp : IsProperMap Jk := (deckHomeo k).isProperMap.comp hJp.1
    have hi : Function.Injective Jk := (MulAction.injective k).comp hJp.2.injective
    have he : Set.range Jk = L i := hk
    rw [←he]
    exact actual_h2_proper_line_separates Jk hp hi (F R) (by rw [he]; exact hR i)
  choose U V hU hV hUc hVc hdis hcover hfrontU hfrontV using hsides
  have hlocal : LocallyFinite L := actual_distinct_lift_family_locally_finite q hq b J g hJ hJperiod
  have hconn (i : I) : IsPreconnected (L i) := by
    obtain ⟨k,hk⟩ := i.2
    change Ranges k=L i at hk
    rw [←hk]
    exact (isConnected_range ((hdeck k).continuous.comp J.continuous)).isPreconnected
  have hpair : Pairwise fun i j : I => Disjoint (L i) (L j) := by
    intro i j hij
    obtain ⟨k,hk⟩ := i.2
    change Ranges k=L i at hk
    obtain ⟨l,hl⟩ := j.2
    change Ranges l=L j at hl
    rw [←hk,←hl]
    apply actual_distinct_target_lift_ranges_disjoint q hq id b J g hJ hJperiod
    intro he
    apply hij
    apply Subtype.ext
    exact hk.symm.trans (he.trans hl)
  have hfinite (r s : ℝ) : {t | t ∈ Set.Icc r s ∧ ∃ i : I, F t ∈ L i}.Finite := by
    have hf := finite_actual_curve_contact_parameters a b ht.1 r s
    apply hf.subset
    intro t ht
    exact ⟨ht.1,by rw [←hF]; exact (hcontacts t).mp ht.2⟩
  have hline (n : ℕ) (i : I) (x : H2) : η^[n] x ∈ L (σ^[n] i) ↔ x ∈ L i :=
    actual_lift_family_deck_permutation_iterates J g σ hσ n i x
  have hJconn : IsConnected (Set.range J) := isConnected_range J.continuous
  have hJinv : ∀ x ∈ Set.range J, η x ∈ Set.range J := by
    rintro _ ⟨t,rfl⟩
    exact ⟨t+2*Real.pi,hJperiod t⟩
  have hfamily (i : I) : L i=Set.range J ∨ Disjoint (L i) (Set.range J) := by
    by_cases he : L i=Set.range J
    · exact Or.inl he
    · right
      obtain ⟨k,hk⟩ := i.2
      change Ranges k=L i at hk
      have h1 : Ranges 1=Set.range J := by simp [Ranges]
      rw [←hk,←h1]
      apply actual_distinct_target_lift_ranges_disjoint q hq id b J g hJ hJperiod
      intro hh
      exact he (hk.symm.trans (hh.trans h1))
  have hcross (i : I) (t : ℝ) (htL : F t ∈ L i) :
      ∀ r s : ℝ, r<t → t<s → ∃ l w : ℝ, r<l ∧ l<t ∧ t<w ∧ w<s ∧
        ((F l ∈ U i ∧ F w ∈ V i) ∨ (F l ∈ V i ∧ F w ∈ U i)) := by
    obtain ⟨k,hk⟩ := i.2
    change Ranges k=L i at hk
    have ht' : F t ∈ Ranges k := hk.symm ▸ htL
    change Set.range (fun v : ℝ => k • J v)=L i at hk
    exact actual_transverse_lift_switches_global_sides q hq hdeck a b ht F J g
      hFp.2.injective hF hJ hJperiod k t ht' (U i) (V i) (hU i) (hV i) (hdis i)
      (by rw [hk]; exact hcover i) (by rw [hk]; exact hfrontU i) (by rw [hk]; exact hfrontV i)
  obtain ⟨i,r,s,hrs,hr,hs,hclean⟩ := periodic_separating_family_has_clean_return
    F η σ L U V hU hV hdis hcover hlocal hconn hpair hfinite hline
    (Set.range J) hJconn hJinv hfamily (2*Real.pi) (by positivity)
    hFperiod hcross R u i₀ hRu huR hR hi₀
  have hclean' : ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image := by
    intro x hx hxb
    obtain ⟨j,hj⟩ := (hcontacts x).mpr hxb
    exact hclean x hx j hj
  have hshort : s-r<2*Real.pi := clean_actual_curve_interval_short a b ht.1 hcount r s
    (fun x hx => by rw [←hF]; exact hclean' x hx)
  obtain ⟨k,hk⟩ := i.2
  change Ranges k=L i at hk
  obtain ⟨t,ht'⟩ := (show F r ∈ Ranges k from hk.symm ▸ hr)
  obtain ⟨v,hv'⟩ := (show F s ∈ Ranges k from hk.symm ▸ hs)
  have htv : t≠v := by
    intro he
    have hsame : F r=F s := ht'.symm.trans (by rw [he]; exact hv')
    exact hrs.ne (hFp.2.injective hsame)
  exact ⟨r,s,t,v,hrs,hshort,htv,k,ht'.symm,hv'.symm,hclean'⟩

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem actual_target_contact_gap_independent_of_lift_representative
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (b : Curve X) (J : ℝ → H2) (g : G) (hinj : Function.Injective J)
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k l : G) (t v t' v' : ℝ)
    (ht : k • J t=l • J t') (hv : k • J v=l • J v') : |v-t|=|v'-t'| := by
  have hdata := reused_curve_lift_integer_period_and_stabilizer q hq id b J g hJ hperiod
  have ht' : (l⁻¹*k) • J t=J t' := by
    have hh := congrArg (fun z : H2 => l⁻¹ • z) ht
    simpa only [smul_smul,inv_mul_cancel,one_smul] using hh
  have hv' : (l⁻¹*k) • J v=J v' := by
    have hh := congrArg (fun z : H2 => l⁻¹ • z) hv
    simpa only [smul_smul,inv_mul_cancel,one_smul] using hh
  obtain ⟨n,hn⟩ := hdata.2 (l⁻¹*k) t t' ht'
  have htparam : t+n*(2*Real.pi)=t' := by
    apply hinj
    rw [hdata.1,←hn]
    exact ht'
  have hvparam : v+n*(2*Real.pi)=v' := by
    apply hinj
    rw [hdata.1,←hn]
    exact hv'
  congr 1
  linarith

private theorem actual_bounded_source_window_has_finite_target_contact_gaps
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (hfinite : (a.image ∩ b.image).Finite)
    (F J : C(ℝ,H2)) (g : G) (hinj : Function.Injective J)
    (hF : ∀ t : ℝ, q (F t)=a.map (Circle.exp t))
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (R T : ℝ) :
    {d : ℝ | ∃ r s t v : ℝ, ∃ k : G,
      r ∈ Set.Icc R T ∧ s ∈ Set.Icc R T ∧ F r=k • J t ∧ F s=k • J v ∧ d=|v-t|}.Finite := by
  classical
  letI : T2Space X := isometric_quotient_cover_hausdorff q hq hdeck
  let Ranges : G → Set H2 := fun k => Set.range (fun t : ℝ => k • J t)
  let I := Set.range Ranges
  let repr (i : I) : G := Classical.choose i.2
  have hrepr (i : I) : Ranges (repr i)=(i : Set H2) := Classical.choose_spec i.2
  let K : Set H2 := F '' Set.Icc R T
  have hK : IsCompact K := isCompact_Icc.image F.continuous
  let D : Set I := {i | ((i : Set H2) ∩ K).Nonempty}
  have hD : D.Finite := compact_meets_finitely_many_actual_h2_lifts q hq hdeck b J g hJ hperiod K hK
  let S : Set ℝ := {r | r ∈ Set.Icc R T ∧ a.map (Circle.exp r) ∈ b.image}
  have hS : S.Finite := finite_actual_curve_contact_parameters a b hfinite R T
  let gap : I × ℝ × ℝ → ℝ := fun p =>
    |Function.invFun J ((repr p.1)⁻¹ • F p.2.2) - Function.invFun J ((repr p.1)⁻¹ • F p.2.1)|
  apply ((hD.prod (hS.prod hS)).image gap).subset
  rintro d ⟨r,s,t,v,k,hrR,hsR,hr,hs,rfl⟩
  let i : I := ⟨Ranges k,⟨k,rfl⟩⟩
  have hiD : i ∈ D := ⟨F r,⟨t,hr.symm⟩,⟨r,hrR,rfl⟩⟩
  have hrS : r ∈ S := by
    refine ⟨hrR,?_⟩
    rw [←hF,hr,hq.map_smul,hJ]
    exact Set.mem_range_self _
  have hsS : s ∈ S := by
    refine ⟨hsR,?_⟩
    rw [←hF,hs,hq.map_smul,hJ]
    exact Set.mem_range_self _
  have hrRep : F r ∈ Ranges (repr i) := by rw [hrepr]; exact ⟨t,hr.symm⟩
  have hsRep : F s ∈ Ranges (repr i) := by rw [hrepr]; exact ⟨v,hs.symm⟩
  obtain ⟨t',ht'⟩ := hrRep
  obtain ⟨v',hv'⟩ := hsRep
  refine ⟨(i,r,s),⟨hiD,hrS,hsS⟩,?_⟩
  have hgap := actual_target_contact_gap_independent_of_lift_representative q hq b J g hinj hJ hperiod
    k (repr i) t v t' v' (hr.symm.trans ht'.symm) (hs.symm.trans hv'.symm)
  change |Function.invFun J ((repr i)⁻¹ • F s) - Function.invFun J ((repr i)⁻¹ • F r)|=|v-t|
  rw [←ht',←hv',inv_smul_smul,inv_smul_smul,
    Function.leftInverse_invFun hinj,Function.leftInverse_invFun hinj]
  exact hgap.symm

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem real_short_interval_period_normalization
    (T r s : ℝ) (hT : 0<T) (hrs : r<s) (hshort : s-r<T) :
    ∃ n : ℤ, 0≤r+n*T ∧ r+n*T<T ∧ r+n*T<s+n*T ∧ s+n*T<2*T := by
  let f : ℤ := Int.floor (r/T)
  have hlo : (f : ℝ)≤r/T := Int.floor_le (r/T)
  have hhi : r/T<(f : ℝ)+1 := Int.lt_floor_add_one (r/T)
  have hlo' := (le_div_iff₀ hT).mp hlo
  have hhi' := (div_lt_iff₀ hT).mp hhi
  refine ⟨-f,?_,?_,?_,?_⟩ <;> simp only [Int.cast_neg] <;> nlinarith

private theorem actual_clean_return_normalizes_source_period_window
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (a b : Curve X) (F J : ℝ → H2) (g : G)
    (hF : ∀ x : ℝ, q (F x)=a.map (Circle.exp x))
    (hperiod : ∀ x : ℝ, F (x+2*Real.pi)=g • F x)
    (r s t v : ℝ) (k : G) (hrs : r<s) (hshort : s-r<2*Real.pi)
    (hr : F r=k • J t) (hs : F s=k • J v)
    (hclean : ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image) :
    ∃ r' s' : ℝ, ∃ k' : G, 0≤r' ∧ r'<2*Real.pi ∧ r'<s' ∧ s'<4*Real.pi ∧
      s'-r'=s-r ∧ F r'=k' • J t ∧ F s'=k' • J v ∧
      ∀ x ∈ Set.Ioo r' s', q (F x) ∉ b.image := by
  obtain ⟨n,hn0,hnT,hnrs,hns⟩ := real_short_interval_period_normalization
    (2*Real.pi) r s (by positivity) hrs hshort
  have hint := (reused_curve_lift_integer_period_and_stabilizer q hq id a F g hF hperiod).1
  refine ⟨r+n*(2*Real.pi),s+n*(2*Real.pi),g^n*k,hn0,hnT,hnrs,?_,?_,?_,?_,?_⟩
  · nlinarith
  · ring
  · rw [hint,hr,mul_smul]
  · rw [hint,hs,mul_smul]
  · intro x hx
    let y : ℝ := x-n*(2*Real.pi)
    have hy : y ∈ Set.Ioo r s := by dsimp [y]; constructor <;> linarith [hx.1,hx.2]
    have hxy : x=y+n*(2*Real.pi) := by dsimp [y]; ring
    rw [hxy,hint,hq.map_smul]
    exact hclean y hy

private theorem actual_periodic_h2_clean_return_minimizes_target_gap
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b) (hcount : 2≤(a.image ∩ b.image).ncard)
    (F J : C(ℝ,H2)) (g : G) (ε : ℝ) (hε : 0<ε)
    (hdisp : ∀ z : H2, ε≤dist z (g • z))
    (hF : ∀ t : ℝ, q (F t)=a.map (Circle.exp t))
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hFperiod : ∀ t : ℝ, F (t+2*Real.pi)=g • F t)
    (hJperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t) :
    ∃ r s t v : ℝ, ∃ k : G,
      r<s ∧ s-r<2*Real.pi ∧ t≠v ∧ F r=k • J t ∧ F s=k • J v ∧
      (∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image) ∧
      ∀ r' s' t' v' : ℝ, ∀ k' : G, r'<s' → s'-r'<2*Real.pi →
        F r'=k' • J t' → F s'=k' • J v' →
        (∀ x ∈ Set.Ioo r' s', q (F x) ∉ b.image) → |v-t|≤|v'-t'| := by
  classical
  let D : Set ℝ := {d | ∃ r s t v : ℝ, ∃ k : G,
    r<s ∧ s-r<2*Real.pi ∧ t≠v ∧ F r=k • J t ∧ F s=k • J v ∧
    (∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image) ∧ d=|v-t|}
  have hFp := actual_uniform_displacement_periodic_lift_closed_embedding q a F g
    (hdeck g) ε hε hdisp hF hFperiod
  have hJp := actual_uniform_displacement_periodic_lift_closed_embedding q b J g
    (hdeck g) ε hε hdisp hJ hJperiod
  have hDfinite : D.Finite := by
    have hbounded := actual_bounded_source_window_has_finite_target_contact_gaps q hq hdeck a b ht.1
      F J g hJp.2.injective hF hJ hJperiod 0 (4*Real.pi)
    apply hbounded.subset
    rintro d ⟨r,s,t,v,k,hrs,hshort,htv,hr,hs,hclean,he⟩
    obtain ⟨r',s',k',hr0,hrT,hrs',hsT,hwidth,hr',hs',hclean'⟩ :=
      actual_clean_return_normalizes_source_period_window q hq a b F J g hF hFperiod
        r s t v k hrs hshort hr hs hclean
    exact ⟨r',s',t,v,k',⟨hr0,by linarith [Real.pi_pos]⟩,
      ⟨hr0.trans hrs'.le,hsT.le⟩,hr',hs',he⟩
  have hDnonempty : D.Nonempty := by
    obtain ⟨r,s,t,v,hrs,hshort,htv,k,hr,hs,hclean⟩ := actual_periodic_h2_clean_same_lift_return
      q hq hdeck a b ht hcount F J g ε hε hdisp hF hJ hFperiod hJperiod
    exact ⟨|v-t|,r,s,t,v,k,hrs,hshort,htv,hr,hs,hclean,rfl⟩
  have hleast := hDnonempty.isLeast_csInf hDfinite
  obtain ⟨r,s,t,v,k,hrs,hshort,htv,hr,hs,hclean,he⟩ := hleast.1
  refine ⟨r,s,t,v,k,hrs,hshort,htv,hr,hs,hclean,?_⟩
  intro r' s' t' v' k' hrs' hshort' hr' hs' hclean'
  have htv' : t'≠v' := by
    intro htveq
    have hsame : F r'=F s' := hr'.trans (by rw [htveq]; exact hs'.symm)
    exact hrs'.ne (hFp.2.injective hsame)
  have hm : |v'-t'| ∈ D := ⟨r',s',t',v',k',hrs',hshort',htv',hr',hs',hclean',rfl⟩
  rw [←he]
  exact hleast.2 hm

end CurveComplex.Hyperbolic



open Set Topology Schoenflies

private theorem clean_embedded_lift_pair_is_jordan_boundary
    (F J : C(ℝ,Plane)) (hF : Function.Injective F) (hJ : Function.Injective J)
    (r s t v : ℝ) (hrs : r<s) (htv : t≠v)
    (hr : F r=J t) (hs : F s=J v)
    (hclean : ∀ x ∈ Set.Ioo r s, F x ∉ Set.range J) :
    IsJordanCurve
      ((fun x : ℝ => F (r+(s-r)*x)) '' unitInterval ∪
        (fun x : ℝ => J (v+(t-v)*x)) '' unitInterval) := by
  let α : ℝ → Plane := fun x => F (r+(s-r)*x)
  let β : ℝ → Plane := fun x => J (v+(t-v)*x)
  have hαcont : Continuous α := F.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hβcont : Continuous β := J.continuous.comp (continuous_const.add (continuous_const.mul continuous_id))
  have hαinj : Function.Injective α := by
    intro x y he
    have hh := hF he
    change r+(s-r)*x=r+(s-r)*y at hh
    nlinarith
  have hβinj : Function.Injective β := by
    intro x y he
    have hh := hJ he
    change v+(t-v)*x=v+(t-v)*y at hh
    have hne : t-v≠0 := sub_ne_zero.mpr htv
    exact mul_left_cancel₀ hne (by linarith)
  have hα0 : α 0=F r := by simp [α]
  have hα1 : α 1=F s := by simp [α]
  have hβ0 : β 0=F s := by simp [β,hs]
  have hβ1 : β 1=F r := by simp [β,hr]
  have hA : IsArcBetween (α '' unitInterval) (F r) (F s) :=
    ⟨α,hαcont.continuousOn,hαinj.injOn,rfl,hα0,hα1⟩
  have hB : IsArcBetween (β '' unitInterval) (F s) (F r) :=
    ⟨β,hβcont.continuousOn,hβinj.injOn,rfl,hβ0,hβ1⟩
  apply IsJordanCurve.of_two_arcs hA hB
  rintro z ⟨x,hx,hxz⟩ ⟨y,hy,hyz⟩
  by_cases hx0 : x=0
  · subst x
    exact Or.inl (hxz.symm.trans hα0)
  by_cases hx1 : x=1
  · subst x
    exact Or.inr (hxz.symm.trans hα1)
  have hx' : 0<x ∧ x<1 := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0),lt_of_le_of_ne hx.2 hx1⟩
  have hparam : r+(s-r)*x ∈ Set.Ioo r s := by constructor <;> nlinarith [hx'.1,hx'.2]
  have hmem : F (r+(s-r)*x) ∈ Set.range J :=
    ⟨v+(t-v)*y,hyz.trans hxz.symm⟩
  exact False.elim (hclean _ hparam hmem)

private theorem affine_parameter_unit_interval_image (a b : ℝ) :
    (fun x : ℝ => a+(b-a)*x) '' unitInterval=Set.uIcc a b := by
  have hI : (unitInterval : Set ℝ)=Set.uIcc 0 1 := by simp [Set.uIcc_of_le (by norm_num : (0:ℝ)≤1)]
  rw [hI]
  have he : (fun x : ℝ => a+(b-a)*x)=(fun y : ℝ => y+a) ∘ (fun x : ℝ => x*(b-a)) := by
    funext x
    simp only [Function.comp_def]
    ring
  rw [he,Set.image_comp,Set.image_mul_const_uIcc,Set.image_add_const_uIcc]
  simp

private theorem parametrized_segment_image_eq_unordered_interval_image
    {P : Type} (F : ℝ → P) (a b : ℝ) :
    (fun x : ℝ => F (a+(b-a)*x)) '' unitInterval=F '' Set.uIcc a b := by
  change (F ∘ fun x : ℝ => a+(b-a)*x) '' unitInterval=F '' Set.uIcc a b
  rw [Set.image_comp,affine_parameter_unit_interval_image]

open Set Topology

private theorem proper_real_line_exits_compact_both_directions
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (K : Set P) (hK : IsCompact K) (u : ℝ) :
    ∃ R T : ℝ, R<u ∧ u<T ∧ F R ∉ K ∧ F T ∉ K := by
  have hpre := hF.isCompact_preimage hK
  obtain ⟨A,hA⟩ := hpre.bddAbove
  obtain ⟨B,hB⟩ := hpre.bddBelow
  refine ⟨min B u-1,max A u+1,?_,?_,?_,?_⟩
  · linarith [min_le_right B u]
  · linarith [le_max_right A u]
  · intro h
    have hh := hB h
    linarith [min_le_left B u]
  · intro h
    have hh := hA h
    linarith [le_max_left A u]

namespace CurveComplex.Hyperbolic
private theorem proper_line_has_first_boundary_contacts_around_inside_point
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (L U V K : Set P) (hK : IsCompact K)
    (hLK : L ⊆ K) (hUK : U ⊆ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (hfinite : ∀ R T : ℝ, {t | t ∈ Set.Icc R T ∧ F t ∈ L}.Finite)
    (u : ℝ) (hu : F u ∈ U) :
    ∃ r s : ℝ, r<u ∧ u<s ∧ F r ∈ L ∧ F s ∈ L ∧
      ∀ t ∈ Set.Ioo r s, F t ∈ U := by
  classical
  have huL : F u ∉ L := by
    have hm : F u ∈ Lᶜ := by rw [←hcover]; exact Or.inl hu
    exact hm
  obtain ⟨R,T,hRu,huT,hRK,hTK⟩ := proper_real_line_exits_compact_both_directions F hF K hK u
  have houtside (t : ℝ) (htK : F t ∉ K) : F t ∈ V := by
    have htL : F t ∉ L := fun htL => htK (hLK htL)
    have hside : F t ∈ U ∪ V := by rw [hcover]; exact htL
    rcases hside with htU | htV
    · exact False.elim (htK (hUK htU))
    · exact htV
  obtain ⟨r₀,hr₀,hr₀L⟩ := interval_separator_contact F hF.continuous L V U hV hU
    hdis.symm (by rw [union_comm,hcover]) R u hRu (houtside R hRK) hu
  obtain ⟨s₀,hs₀,hs₀L⟩ := interval_separator_contact F hF.continuous L U V hU hV
    hdis hcover u T huT hu (houtside T hTK)
  let A : Set ℝ := {t | t ∈ Set.Icc R u ∧ F t ∈ L}
  let B : Set ℝ := {t | t ∈ Set.Icc u T ∧ F t ∈ L}
  have hA : A.Finite := hfinite R u
  have hB : B.Finite := hfinite u T
  have hAn : A.Nonempty := ⟨r₀,⟨hr₀.1.le,hr₀.2.le⟩,hr₀L⟩
  have hBn : B.Nonempty := ⟨s₀,⟨hs₀.1.le,hs₀.2.le⟩,hs₀L⟩
  have hgreat := hAn.isGreatest_csSup hA
  have hleast := hBn.isLeast_csInf hB
  let r := sSup A
  let s := sInf B
  have hrA : r ∈ A := hgreat.1
  have hsB : s ∈ B := hleast.1
  have hru : r<u := lt_of_le_of_ne hrA.1.2 (by intro he; exact huL (he ▸ hrA.2))
  have hus : u<s := lt_of_le_of_ne hsB.1.1 (by intro he; exact huL (he.symm ▸ hsB.2))
  have havoid (t : ℝ) (ht : t ∈ Set.Ioo r s) : F t ∉ L := by
    intro htL
    rcases lt_trichotomy t u with htu | he | hut
    · have htA : t ∈ A := ⟨⟨hrA.1.1.trans ht.1.le,htu.le⟩,htL⟩
      have hh := hgreat.2 htA
      exact (not_le_of_gt ht.1) hh
    · exact huL (he ▸ htL)
    · have htB : t ∈ B := ⟨⟨hut.le,ht.2.le.trans hsB.1.2⟩,htL⟩
      have hh := hleast.2 htB
      exact (not_le_of_gt ht.2) hh
  have hsub : F '' Set.Ioo r s ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hcover]
    exact havoid t ht
  have hconn := (isPreconnected_Ioo (a := r) (b := s)).image F hF.continuous.continuousOn
  rcases hconn.subset_or_subset hU hV hdis hsub with hinside | hout
  · exact ⟨r,s,hru,hus,hrA.2,hsB.2,fun t ht => hinside ⟨t,ht,rfl⟩⟩
  · have huV : F u ∈ V := hout ⟨u,⟨hru,hus⟩,rfl⟩
    exact False.elim (Set.disjoint_left.mp hdis hu huV)

private theorem proper_line_disjoint_boundary_lies_outside_bounded_inside
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (L U V K : Set P) (hK : IsCompact K) (hUK : U ⊆ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (havoid : ∀ t : ℝ, F t ∉ L) : Set.range F ⊆ V := by
  have hsub : Set.range F ⊆ U ∪ V := by
    rintro _ ⟨t,rfl⟩
    rw [hcover]
    exact havoid t
  rcases (isPreconnected_range hF.continuous).subset_or_subset hU hV hdis hsub with hinside | hout
  · have huniv : F ⁻¹' K=Set.univ := by
      apply Set.eq_univ_of_forall
      intro t
      exact hUK (hinside ⟨t,rfl⟩)
    have hc := hF.isCompact_preimage hK
    rw [huniv] at hc
    exact False.elim (noncompact_univ ℝ hc)
  · exact hout

private theorem proper_line_upper_tail_disjoint_boundary_lies_outside
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (L U V K : Set P) (hK : IsCompact K) (hUK : U ⊆ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (a : ℝ) (havoid : ∀ t : ℝ, a<t → F t ∉ L) : F '' Set.Ioi a ⊆ V := by
  have hsub : F '' Set.Ioi a ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hcover]
    exact havoid t ht
  have hconn := (isPreconnected_Ioi (a := a)).image F hF.continuous.continuousOn
  rcases hconn.subset_or_subset hU hV hdis hsub with hinside | hout
  · obtain ⟨B,hB⟩ := (hF.isCompact_preimage hK).bddAbove
    have ha : a < max a B+1 := by linarith [le_max_left a B]
    have hpoint : F (max a B+1) ∈ K := hUK (hinside ⟨_,ha,rfl⟩)
    have hh := hB hpoint
    exact False.elim (by linarith [le_max_right a B])
  · exact hout

private theorem proper_line_lower_tail_disjoint_boundary_lies_outside
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (L U V K : Set P) (hK : IsCompact K) (hUK : U ⊆ K)
    (hU : IsOpen U) (hV : IsOpen V) (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (a : ℝ) (havoid : ∀ t : ℝ, t<a → F t ∉ L) : F '' Set.Iio a ⊆ V := by
  have hsub : F '' Set.Iio a ⊆ U ∪ V := by
    rintro _ ⟨t,ht,rfl⟩
    rw [hcover]
    exact havoid t ht
  have hconn := (isPreconnected_Iio (a := a)).image F hF.continuous.continuousOn
  rcases hconn.subset_or_subset hU hV hdis hsub with hinside | hout
  · obtain ⟨B,hB⟩ := (hF.isCompact_preimage hK).bddBelow
    have ha : min a B-1<a := by linarith [min_le_left a B]
    have hpoint : F (min a B-1) ∈ K := hUK (hinside ⟨_,ha,rfl⟩)
    have hh := hB hpoint
    exact False.elim (by linarith [min_le_right a B])
  · exact hout

end CurveComplex.Hyperbolic
namespace CurveComplex.Hyperbolic
open Set Topology Schoenflies
private theorem clean_source_arc_boundary_target_parameter_interval
    {P : Type} (F J : ℝ → P) (hJ : Function.Injective J)
    (r s t v : ℝ) (hrs : r<s) (hr : F r=J t) (hs : F s=J v)
    (hclean : ∀ x ∈ Set.Ioo r s, F x ∉ Set.range J) (u : ℝ) :
    J u ∈ F '' Set.Icc r s ∪ J '' Set.uIcc t v ↔ u ∈ Set.uIcc t v := by
  constructor
  · rintro (⟨x,hx,hxu⟩ | ⟨x,hx,hxu⟩)
    · by_cases hxr : x=r
      · subst x
        have hut : u=t := hJ (hxu.symm.trans hr)
        rw [hut]
        exact Set.left_mem_uIcc
      by_cases hxs : x=s
      · subst x
        have huv : u=v := hJ (hxu.symm.trans hs)
        rw [huv]
        exact Set.right_mem_uIcc
      have hx' : x ∈ Set.Ioo r s :=
        ⟨lt_of_le_of_ne hx.1 (Ne.symm hxr),lt_of_le_of_ne hx.2 hxs⟩
      exact False.elim (hclean x hx' ⟨u,hxu.symm⟩)
    · exact hJ hxu ▸ hx
  · intro hu
    exact Or.inr ⟨u,hu,rfl⟩

private theorem target_proper_line_avoids_inside_clean_lift_bigon
    (F J : C(ℝ,Plane)) (hF : Function.Injective F) (hJ : Function.Injective J)
    (hproper : IsProperMap J) (r s t v : ℝ) (hrs : r<s) (htv : t≠v)
    (hr : F r=J t) (hs : F s=J v)
    (hclean : ∀ x ∈ Set.Ioo r s, F x ∉ Set.range J) :
    Set.range J ⊆ (inside (F '' Set.Icc r s ∪ J '' Set.uIcc t v))ᶜ := by
  let C := F '' Set.Icc r s ∪ J '' Set.uIcc t v
  have hC : IsJordanCurve C := by
    have hh := clean_embedded_lift_pair_is_jordan_boundary F J hF hJ r s t v hrs htv hr hs hclean
    rw [parametrized_segment_image_eq_unordered_interval_image F r s,
      parametrized_segment_image_eq_unordered_interval_image J v t,
      Set.uIcc_of_le hrs.le,Set.uIcc_comm v t] at hh
    exact hh
  have hsep := jordan_curve_theorem hC
  let K := closure (inside C)
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
  have hcontact (u : ℝ) : J u ∈ C ↔ u ∈ Set.uIcc t v :=
    clean_source_arc_boundary_target_parameter_interval F J hJ r s t v hrs hr hs hclean u
  have hupper : J '' Set.Ioi (max t v) ⊆ outside C :=
    proper_line_upper_tail_disjoint_boundary_lies_outside J hproper C (inside C) (outside C) K
      hK subset_closure hsep.isOpen_inside hsep.isOpen_outside disjoint_inside_outside
      (inside_union_outside C) (max t v) (by
        intro u hu huc
        have hh := (hcontact u).mp huc
        exact (not_le_of_gt hu) hh.2)
  have hlower : J '' Set.Iio (min t v) ⊆ outside C :=
    proper_line_lower_tail_disjoint_boundary_lies_outside J hproper C (inside C) (outside C) K
      hK subset_closure hsep.isOpen_inside hsep.isOpen_outside disjoint_inside_outside
      (inside_union_outside C) (min t v) (by
        intro u hu huc
        have hh := (hcontact u).mp huc
        exact (not_le_of_gt hu) hh.1)
  rintro _ ⟨u,rfl⟩ huin
  by_cases hu : u ∈ Set.uIcc t v
  · exact (inside_subset_compl huin) ((hcontact u).mpr hu)
  · rcases lt_or_ge u (min t v) with hum | hmu
    · exact Set.disjoint_left.mp disjoint_inside_outside huin (hlower ⟨u,hum,rfl⟩)
    · have hmax : max t v < u := by
        apply lt_of_not_ge
        intro hum
        exact hu ⟨hmu,hum⟩
      exact Set.disjoint_left.mp disjoint_inside_outside huin (hupper ⟨u,hmax,rfl⟩)

end CurveComplex.Hyperbolic
namespace CurveComplex.Hyperbolic
open Set Topology Schoenflies
private theorem actual_clean_lift_bigon_inside_avoids_projected_target
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (b : Curve X) (F J : C(ℝ,H2)) (g : G)
    (hinjF : Function.Injective F) (hinjJ : Function.Injective J) (hproperJ : IsProperMap J)
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (r s t v : ℝ) (k : G) (hrs : r<s) (htv : t≠v)
    (hr : F r=k • J t) (hs : F s=k • J v)
    (hclean : ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image) :
    ∀ z : H2, hyperbolicPlaneHomeomorph z ∈
      inside ((hyperbolicPlaneHomeomorph ∘ F) '' Set.Icc r s ∪
        (fun x : ℝ => hyperbolicPlaneHomeomorph (k • J x)) '' Set.uIcc t v) → q z ∉ b.image := by
  classical
  let e := hyperbolicPlaneHomeomorph
  let deckHomeo (m : G) : H2 ≃ₜ H2 :=
    { toEquiv :=
        { toFun := fun z => m • z
          invFun := fun z => m⁻¹ • z
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
      continuous_toFun := (hdeck m).continuous
      continuous_invFun := (hdeck m⁻¹).continuous }
  let A : C(ℝ,Plane) := ⟨e ∘ F,e.continuous.comp F.continuous⟩
  let B : C(ℝ,Plane) := ⟨fun x => e (k • J x),e.continuous.comp ((hdeck k).continuous.comp J.continuous)⟩
  have hBproper : IsProperMap B := e.isProperMap.comp ((deckHomeo k).isProperMap.comp hproperJ)
  have hBinj : Function.Injective B := e.injective.comp ((MulAction.injective k).comp hinjJ)
  have hAinj : Function.Injective A := e.injective.comp hinjF
  have hr' : A r=B t := congrArg e hr
  have hs' : A s=B v := congrArg e hs
  have hclean' : ∀ x ∈ Set.Ioo r s, A x ∉ Set.range B := by
    intro x hx ⟨w,hw⟩
    have he : k • J w=F x := e.injective hw
    apply hclean x hx
    rw [←he,hq.map_smul,hJ]
    exact Set.mem_range_self _
  let C := A '' Set.Icc r s ∪ B '' Set.uIcc t v
  have hC : IsJordanCurve C := by
    have hh := clean_embedded_lift_pair_is_jordan_boundary A B hAinj hBinj r s t v hrs htv hr' hs' hclean'
    rw [parametrized_segment_image_eq_unordered_interval_image A r s,
      parametrized_segment_image_eq_unordered_interval_image B v t,
      Set.uIcc_of_le hrs.le,Set.uIcc_comm v t] at hh
    exact hh
  have hsep := jordan_curve_theorem hC
  let K := closure (inside C)
  have hK : IsCompact K := Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure
  intro z hzin hzb
  obtain ⟨l,u,hz⟩ := (actual_target_lift_family_contacts q hq id Function.injective_id b J hJ z).mp hzb
  by_cases hrange : Set.range (fun x : ℝ => l • J x)=Set.range (fun x : ℝ => k • J x)
  · have hzB : z ∈ Set.range (fun x : ℝ => k • J x) := hrange ▸ (show z ∈ Set.range (fun x : ℝ => l • J x) from ⟨u,hz.symm⟩)
    obtain ⟨w,hw⟩ := hzB
    have houtside := target_proper_line_avoids_inside_clean_lift_bigon A B hAinj hBinj hBproper
      r s t v hrs htv hr' hs' hclean'
    exact houtside ⟨w,congrArg e hw⟩ hzin
  · have hdis := actual_distinct_target_lift_ranges_disjoint q hq id b J g hJ hperiod l k hrange
    let M : C(ℝ,Plane) := ⟨fun x => e (l • J x),e.continuous.comp ((hdeck l).continuous.comp J.continuous)⟩
    have hMproper : IsProperMap M := e.isProperMap.comp ((deckHomeo l).isProperMap.comp hproperJ)
    have havoid : ∀ w : ℝ, M w ∉ C := by
      intro w hw
      rcases hw with ⟨x,hx,hxe⟩ | ⟨x,hx,hxe⟩
      · have he : F x=l • J w := e.injective hxe
        have hxL : F x ∈ Set.range (fun x : ℝ => l • J x) := ⟨w,he.symm⟩
        by_cases hxr : x=r
        · subst x
          exact Set.disjoint_left.mp hdis hxL ⟨t,hr.symm⟩
        by_cases hxs : x=s
        · subst x
          exact Set.disjoint_left.mp hdis hxL ⟨v,hs.symm⟩
        have hx' : x ∈ Set.Ioo r s :=
          ⟨lt_of_le_of_ne hx.1 (Ne.symm hxr),lt_of_le_of_ne hx.2 hxs⟩
        apply hclean x hx'
        rw [he,hq.map_smul,hJ]
        exact Set.mem_range_self _
      · have he : k • J x=l • J w := e.injective hxe
        exact Set.disjoint_left.mp hdis ⟨w,rfl⟩ ⟨x,he⟩
    have hout := proper_line_disjoint_boundary_lies_outside_bounded_inside M hMproper C (inside C) (outside C) K
      hK subset_closure hsep.isOpen_inside hsep.isOpen_outside disjoint_inside_outside (inside_union_outside C) havoid
    have hzout : e z ∈ outside C := hout ⟨u,congrArg e hz.symm⟩
    exact Set.disjoint_left.mp disjoint_inside_outside hzin hzout

end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology

private theorem first_exit_endpoints_avoid_interior_boundary_parameter_interval
    {P : Type} (F : ℝ → P) (U L : Set P) (hdis : Disjoint U L)
    (R T r s : ℝ) (hrs : r<s)
    (hboundary : ∀ x ∈ Set.Icc R T, F x ∈ L)
    (hinside : ∀ x ∈ Set.Ioo r s, F x ∈ U) :
    r ∉ Set.Ioo R T ∧ s ∉ Set.Ioo R T := by
  constructor
  · intro hr
    let x : ℝ := (r+min s T)/2
    have hxrs : x ∈ Set.Ioo r s := by
      dsimp [x]
      constructor
      · have hh : r < min s T := lt_min hrs hr.2
        linarith
      · linarith [min_le_left s T]
    have hxRT : x ∈ Set.Icc R T := by
      dsimp [x]
      constructor
      · have hh : r < min s T := lt_min hrs hr.2
        linarith [hr.1]
      · linarith [min_le_right s T,hr.2]
    exact Set.disjoint_left.mp hdis (hinside x hxrs) (hboundary x hxRT)
  · intro hs
    let x : ℝ := (max r R+s)/2
    have hxrs : x ∈ Set.Ioo r s := by
      dsimp [x]
      constructor
      · linarith [le_max_left r R]
      · have hh : max r R<s := max_lt hrs hs.1
        linarith
    have hxRT : x ∈ Set.Icc R T := by
      dsimp [x]
      constructor
      · linarith [le_max_right r R,hs.1]
      · have hh : max r R<s := max_lt hrs hs.1
        linarith [hs.2]
    exact Set.disjoint_left.mp hdis (hinside x hxrs) (hboundary x hxRT)

private theorem parameter_gap_shrinks_from_one_interior_endpoint
    (R T u v : ℝ) (hu : u ∈ Set.Ioo R T) (hv : v ∈ Set.Icc R T) :
    |v-u|<T-R := by
  rw [abs_lt]
  constructor <;> linarith [hu.1,hu.2,hv.1,hv.2]


private theorem first_exit_endpoints_on_target_when_source_is_shifted
    {P : Type} (F M : ℝ → P) (hF : Function.Injective F)
    (U B : Set P) (r s x y d : ℝ) (hrs : r < s) (hxy : x < y)
    (hshift : ∀ u, M u = F (u+d))
    (hdis : Disjoint U (F '' Set.Icc r s ∪ B))
    (hxr : M x ∈ F '' Set.Icc r s ∪ B)
    (hyr : M y ∈ F '' Set.Icc r s ∪ B)
    (hendr : F r ∈ B) (hends : F s ∈ B)
    (hinside : ∀ u ∈ Set.Ioo x y, M u ∈ U) : M x ∈ B ∧ M y ∈ B := by
  have hbnd : ∀ u ∈ Set.Icc (r-d) (s-d), M u ∈ F '' Set.Icc r s ∪ B := by
    intro u hu
    left
    exact ⟨u+d,⟨by linarith [hu.1],by linarith [hu.2]⟩,(hshift u).symm⟩
  have havoid := first_exit_endpoints_avoid_interior_boundary_parameter_interval M U
    (F '' Set.Icc r s ∪ B) hdis (r-d) (s-d) x y hxy hbnd hinside
  have endpoint (u : ℝ) (hu : M u ∈ F '' Set.Icc r s ∪ B)
      (havoid : u ∉ Set.Ioo (r-d) (s-d)) : M u ∈ B := by
    rcases hu with ⟨w,hw,hwe⟩ | hu
    · have he : w=u+d := hF (hwe.trans (hshift u))
      subst w
      by_cases he : u+d=r
      · rw [hshift,he]
        exact hendr
      by_cases he : u+d=s
      · rw [hshift,he]
        exact hends
      exfalso
      apply havoid
      constructor
      · have hh : r < u+d := lt_of_le_of_ne hw.1 (Ne.symm (by assumption))
        linarith
      · have hh : u+d < s := lt_of_le_of_ne hw.2 he
        linarith
    · exact hu
  exact ⟨endpoint x hxr havoid.1,endpoint y hyr havoid.2⟩

private theorem actual_deck_source_first_exit_endpoints_on_target
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (a : Curve X) (F : ℝ → H2) (g m : G)
    (hinj : Function.Injective F)
    (hF : ∀ u, q (F u)=a.map (Circle.exp u))
    (hperiod : ∀ u, F (u+2*Real.pi)=g • F u)
    (U B : Set H2) (r s x y : ℝ) (hrs : r<s) (hxy : x<y)
    (hdis : Disjoint U (F '' Set.Icc r s ∪ B))
    (hx : m • F x ∈ F '' Set.Icc r s ∪ B)
    (hy : m • F y ∈ F '' Set.Icc r s ∪ B)
    (hr : F r ∈ B) (hs : F s ∈ B)
    (hinside : ∀ u ∈ Set.Ioo x y, m • F u ∈ U) :
    m • F x ∈ B ∧ m • F y ∈ B := by
  classical
  by_cases heq : Set.range (fun u : ℝ => m • F u)=Set.range F
  · have hmem : m • F 0 ∈ Set.range F := heq ▸ Set.mem_range_self (f := fun u : ℝ => m • F u) 0
    obtain ⟨w,hw⟩ := hmem
    have hdata := reused_curve_lift_integer_period_and_stabilizer q hq id a F g hF hperiod
    obtain ⟨n,hn⟩ := hdata.2 m 0 w hw.symm
    apply first_exit_endpoints_on_target_when_source_is_shifted F (fun u => m • F u) hinj
      U B r s x y (n*(2*Real.pi)) hrs hxy _ hdis hx hy hr hs hinside
    intro u
    rw [hn,hdata.1]
  · have heq' : Set.range (fun u : ℝ => m • F u) ≠ Set.range (fun u : ℝ => (1 : G) • F u) := by
      simpa only [one_smul] using heq
    have hd := actual_distinct_target_lift_ranges_disjoint q hq id a F g hF hperiod m 1 heq'
    have endpoint (u : ℝ) (hu : m • F u ∈ F '' Set.Icc r s ∪ B) : m • F u ∈ B := by
      rcases hu with ⟨w,hw,hwe⟩ | hu
      · exact False.elim (Set.disjoint_left.mp hd ⟨u,rfl⟩ ⟨w,by simpa using hwe⟩)
      · exact hu
    exact ⟨endpoint x hx,endpoint y hy⟩
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set
private theorem pinned_target_segment_endpoints_have_smaller_gap
    {P : Type} (J M : ℝ → P) (hJ : Function.Injective J)
    (t v θ u x y : ℝ) (hθ : θ ∈ Set.uIoo t v)
    (hpin : M u=J θ) (hxy : x=u ∨ y=u)
    (hx : M x ∈ J '' Set.uIcc t v) (hy : M y ∈ J '' Set.uIcc t v) :
    ∃ τ υ : ℝ, τ ∈ Set.uIcc t v ∧ υ ∈ Set.uIcc t v ∧
      M x=J τ ∧ M y=J υ ∧ |υ-τ| < |v-t| := by
  obtain ⟨τ,hτ,hτeq⟩ := hx
  obtain ⟨υ,hυ,hυeq⟩ := hy
  refine ⟨τ,υ,hτ,hυ,hτeq.symm,hυeq.symm,?_⟩
  have hw : max t v-min t v=|v-t| := by
    rcases le_total t v with h | h
    · rw [max_eq_right h,min_eq_left h,abs_of_nonneg (sub_nonneg.mpr h)]
    · rw [max_eq_left h,min_eq_right h,abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  rcases hxy with hx | hy
  · have he : τ=θ := hJ (hτeq.trans (hx ▸ hpin))
    rw [he,←hw]
    exact parameter_gap_shrinks_from_one_interior_endpoint (min t v) (max t v) θ υ hθ hυ
  · have he : υ=θ := hJ (hυeq.trans (hy ▸ hpin))
    rw [he,abs_sub_comm,←hw]
    exact parameter_gap_shrinks_from_one_interior_endpoint (min t v) (max t v) θ τ hθ hτ
end CurveComplex.Hyperbolic



open Set Topology

private theorem points_of_open_bounded_real_set_between_endpoints
    (S : Set ℝ) (hS : IsOpen S) (hb : BddBelow S) (ha : BddAbove S) :
    ∀ x ∈ S, sInf S<x ∧ x<sSup S := by
  intro x hx
  obtain ⟨δ,hδ,hball⟩ := Metric.mem_nhds_iff.mp (hS.mem_nhds hx)
  have hl : x-δ/2 ∈ S := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  have hr : x+δ/2 ∈ S := by
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith
  constructor
  · have hh := csInf_le hb hl
    linarith
  · have hh := le_csSup ha hr
    linarith

private theorem proper_real_line_inside_component_has_boundary_endpoints
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (U L K : Set P) (hU : IsOpen U) (hfront : frontier U=L)
    (hK : IsCompact K) (hUK : U ⊆ K) (u : ℝ) (hu : F u ∈ U) :
    ∃ r s : ℝ, r<u ∧ u<s ∧ F r ∈ L ∧ F s ∈ L ∧
      ∀ t ∈ Set.Ioo r s, F t ∈ U := by
  let S : Set ℝ := F ⁻¹' U
  let C : Set ℝ := connectedComponentIn S u
  have huS : u ∈ S := hu
  have huC : u ∈ C := mem_connectedComponentIn huS
  have hCsub : C ⊆ S := connectedComponentIn_subset S u
  have hSopen : IsOpen S := hU.preimage hF.continuous
  have hCopen : IsOpen C := hSopen.connectedComponentIn
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr huS
  have hCbound : C ⊆ F ⁻¹' K := fun t ht => hUK (hCsub ht)
  have hpre := hF.isCompact_preimage hK
  have hb : BddBelow C := hpre.bddBelow.mono hCbound
  have ha : BddAbove C := hpre.bddAbove.mono hCbound
  have hstrict := points_of_open_bounded_real_set_between_endpoints C hCopen hb ha
  have hleft : sInf C ∉ C := fun hx => (lt_irrefl _) (hstrict _ hx).1
  have hright : sSup C ∉ C := fun hx => (lt_irrefl _) (hstrict _ hx).2
  have hcl (x : ℝ) (hx : x ∈ closure C) : F x ∈ closure U := by
    apply (closure_minimal (s := C) (t := F ⁻¹' closure U) ?_
      (isClosed_closure.preimage hF.continuous)) hx
    exact fun t ht => subset_closure (hCsub ht)
  have hrelative : ∀ x ∈ closure C, x ∈ S → x ∈ C := by
    obtain ⟨D,hD,he⟩ := IsInducing.subtypeVal.image_eq_isClosed_inter_range
      (isClosed_connectedComponent (x := (⟨u,huS⟩ : S)))
    have he' : C=D ∩ S := by
      change connectedComponentIn S u=D ∩ S
      rw [connectedComponentIn_eq_image huS]
      simpa using he
    intro x hx hxS
    rw [he'] at hx ⊢
    exact ⟨(closure_minimal Set.inter_subset_left hD) hx,hxS⟩
  have hleftcl : sInf C ∈ closure C := csInf_mem_closure ⟨u,huC⟩ hb
  have hrightcl : sSup C ∈ closure C := csSup_mem_closure ⟨u,huC⟩ ha
  have hfrontier (x : ℝ) (hx : x ∈ closure C) (hxC : x ∉ C) : F x ∈ L := by
    rw [←hfront]
    rw [frontier,hU.interior_eq]
    refine ⟨hcl x hx,?_⟩
    exact fun hxU => hxC (hrelative x hx hxU)
  exact ⟨sInf C,sSup C,(hstrict u huC).1,(hstrict u huC).2,
    hfrontier _ hleftcl hleft,hfrontier _ hrightcl hright,
    fun t ht => hCsub (hCconn.Ioo_csInf_csSup_subset hb ha ht)⟩

private theorem proper_line_first_exit_keeps_isolated_entry_contact
    {P : Type} [TopologicalSpace P] (F : ℝ → P) (hF : IsProperMap F)
    (U L K : Set P) (hU : IsOpen U) (hfront : frontier U=L)
    (hK : IsCompact K) (hUK : U ⊆ K) (u δ : ℝ) (hδ : 0<δ)
    (huL : F u ∈ L)
    (hunique : ∀ t ∈ Set.Ioo (u-δ) (u+δ), F t ∈ L → t=u)
    (hentry : ∃ v ∈ Set.Ioo (u-δ) (u+δ), F v ∈ U) :
    ∃ r s : ℝ, r<s ∧ F r ∈ L ∧ F s ∈ L ∧
      (r=u ∨ s=u) ∧ ∀ t ∈ Set.Ioo r s, F t ∈ U := by
  have huNotU : F u ∉ U := by
    have hh : F u ∈ frontier U := hfront.symm ▸ huL
    change F u ∈ closure U \ interior U at hh
    simpa only [hU.interior_eq] using hh.2
  obtain ⟨v,hv,hvU⟩ := hentry
  obtain ⟨r,s,hrv,hvs,hrL,hsL,hinside⟩ :=
    proper_real_line_inside_component_has_boundary_endpoints F hF U L K hU hfront hK hUK v hvU
  have hvne : v≠u := by intro he; exact huNotU (he ▸ hvU)
  refine ⟨r,s,hrv.trans hvs,hrL,hsL,?_,hinside⟩
  rcases lt_or_gt_of_ne hvne with hvu | huv
  · right
    rcases lt_trichotomy s u with hsu | he | hus
    · exact hunique s ⟨hv.1.trans hvs,hsu.trans (by linarith)⟩ hsL
    · exact he
    · exact False.elim (huNotU (hinside u ⟨hrv.trans hvu,hus⟩))
  · left
    rcases lt_trichotomy r u with hru | he | hur
    · exact False.elim (huNotU (hinside u ⟨hru,huv.trans hvs⟩))
    · exact he
    · exact hunique r ⟨(by linarith),hrv.trans hv.2⟩ hrL

namespace CurveComplex.Hyperbolic
open Set Topology
private theorem embedded_lift_target_axis_contact_is_isolated
    {P : Type} [TopologicalSpace P] (F : C(ℝ,P)) (hinj : Function.Injective F)
    (K : OpenPartialHomeomorph P (ℝ × ℝ)) (L : Set P) (u : ℝ)
    (huK : F u ∈ K.source) (hzero : K (F u)=(0,0))
    (hsourceaxis : ∀ t : ℝ, F t ∈ K.source → (K (F t)).1=0)
    (htargetaxis : ∀ x ∈ K.source, x ∈ L ↔ (K x).2=0) :
    ∃ δ : ℝ, 0<δ ∧ ∀ t ∈ Set.Ioo (u-δ) (u+δ), F t ∈ L ↔ t=u := by
  obtain ⟨δ,hδ,hsigns⟩ := embedded_lift_crossing_chart_coordinate_signs F hinj K u huK hzero hsourceaxis
  refine ⟨δ,hδ,?_⟩
  intro t ht
  constructor
  · intro htL
    by_contra hne
    rcases lt_or_gt_of_ne hne with htu | hut
    · obtain ⟨htK,_,hsg⟩ := hsigns t (u+δ/2) ht.1 htu (by linarith) (by linarith)
      have hz := (htargetaxis _ htK).mp htL
      rcases hsg with ⟨hl,_⟩ | ⟨hl,_⟩ <;> linarith
    · obtain ⟨_,htK,hsg⟩ := hsigns (u-δ/2) t (by linarith) (by linarith) hut ht.2
      have hz := (htargetaxis _ htK).mp htL
      rcases hsg with ⟨_,hl⟩ | ⟨_,hl⟩ <;> linarith
  · intro he
    rw [he]
    exact (htargetaxis _ huK).mpr (by rw [hzero])


private theorem proper_chart_crossing_has_pinned_inside_component
    {P : Type} [TopologicalSpace P] (F : C(ℝ,P))
    (hinj : Function.Injective F) (hproper : IsProperMap F)
    (L U V A : Set P) (hU : IsOpen U) (hV : IsOpen V)
    (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (hfrontU : frontier U=L) (hfrontV : frontier V=L)
    (hA : IsCompact A) (hUA : U ⊆ A)
    (K : OpenPartialHomeomorph P (ℝ × ℝ)) (u : ℝ)
    (huK : F u ∈ K.source) (hzero : K (F u)=(0,0))
    (hsourceaxis : ∀ t : ℝ, F t ∈ K.source → (K (F t)).1=0)
    (htargetaxis : ∀ z ∈ K.source, z ∈ L ↔ (K z).2=0) :
    ∃ x y : ℝ, x<y ∧ F x ∈ L ∧ F y ∈ L ∧ (x=u ∨ y=u) ∧
      ∀ t ∈ Set.Ioo x y, F t ∈ U := by
  obtain ⟨δ,hδ,hiso⟩ := embedded_lift_target_axis_contact_is_isolated F hinj K L u
    huK hzero hsourceaxis htargetaxis
  obtain ⟨l,w,h1,h2,h3,h4,hside⟩ := actual_embedded_lift_crosses_global_sides F hinj
    L U V hU hV hdis hcover hfrontU hfrontV K u huK hzero hsourceaxis htargetaxis
    (u-δ) (u+δ) (by linarith) (by linarith)
  have hentry : ∃ v ∈ Set.Ioo (u-δ) (u+δ), F v ∈ U := by
    rcases hside with hside | hside
    · exact ⟨l,⟨h1,by linarith⟩,hside.1⟩
    · exact ⟨w,⟨by linarith,h4⟩,hside.2⟩
  apply proper_line_first_exit_keeps_isolated_entry_contact F hproper U L A
    hU hfrontU hA hUA u δ hδ
    ((htargetaxis _ huK).mpr (by rw [hzero]))
    (fun t ht h => (hiso t ht).mp h) hentry
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology
private theorem actual_transverse_local_boundary_has_pinned_inside_component
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b) (F J : C(ℝ,H2)) (g : G)
    (hinj : Function.Injective F) (hproper : IsProperMap F)
    (hF : ∀ t : ℝ, q (F t)=a.map (Circle.exp t))
    (hJ : ∀ t : ℝ, q (J t)=b.map (Circle.exp t))
    (hperiod : ∀ t : ℝ, J (t+2*Real.pi)=g • J t)
    (k : G) (u : ℝ) (hu : F u ∈ Set.range (fun t : ℝ => k • J t))
    (L U V A W : Set H2) (hU : IsOpen U) (hV : IsOpen V)
    (hdis : Disjoint U V) (hcover : U ∪ V=Lᶜ)
    (hfrontU : frontier U=L) (hfrontV : frontier V=L)
    (hA : IsCompact A) (hUA : U ⊆ A)
    (hW : IsOpen W) (huW : F u ∈ W)
    (hlocal : ∀ z ∈ W, z ∈ L ↔ z ∈ Set.range (fun t : ℝ => k • J t)) :
    ∃ x y : ℝ, x<y ∧ F x ∈ L ∧ F y ∈ L ∧ (x=u ∨ y=u) ∧
      ∀ t ∈ Set.Ioo x y, F t ∈ U := by
  letI : T2Space X := isometric_quotient_cover_hausdorff q hq hdeck
  obtain ⟨W₀,hW₀,huW₀,hbranch⟩ := actual_target_lift_contact_local_branch q hq b J g hJ hperiod k (F u) hu
  have hua : q (F u) ∈ a.image := by rw [hF]; exact Set.mem_range_self _
  have hub : q (F u) ∈ b.image := (hbranch (F u) huW₀).mpr hu
  obtain ⟨K,huK,hzero,haxes⟩ := actual_cover_crossing_chart q
    hq.isCoveringMap.isLocalHomeomorph a b (F u) (ht.2 _ ⟨hua,hub⟩)
  let K' := K.restrOpen (W₀ ∩ W) (hW₀.inter hW)
  have huK' : F u ∈ K'.source := ⟨huK,huW₀,huW⟩
  apply proper_chart_crossing_has_pinned_inside_component F hinj hproper L U V A
    hU hV hdis hcover hfrontU hfrontV hA hUA K' u huK'
  · change K (F u)=(0,0)
    exact hzero
  · intro t htK
    change (K (F t)).1=0
    apply (haxes (F t) htK.1).1.mp
    rw [hF]
    exact Set.mem_range_self _
  · intro z hzK
    change z ∈ L ↔ (K z).2=0
    exact (hlocal z hzK.2.2).trans ((hbranch z hzK.2.1).symm.trans (haxes z hzK.1).2)
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology Schoenflies

private theorem embedded_target_segment_is_local_full_boundary
    {P : Type} [TopologicalSpace P] (J : ℝ → P) (hJ : IsEmbedding J)
    (A : Set P) (hA : IsClosed A) (R T u : ℝ) (hu : u ∈ Set.Ioo R T)
    (huA : J u ∉ A) :
    ∃ W : Set P, IsOpen W ∧ J u ∈ W ∧ Disjoint W A ∧
      ∀ x ∈ W, x ∈ A ∪ J '' Set.Icc R T ↔ x ∈ Set.range J := by
  obtain ⟨V,hV,himage⟩ := hJ.isInducing.image_eq_isOpen_inter_range (isOpen_Ioo (a := R) (b := T))
  have huV : J u ∈ V := by
    have hh : J u ∈ J '' Set.Ioo R T := ⟨u,hu,rfl⟩
    rw [himage] at hh
    exact hh.1
  refine ⟨V ∩ Aᶜ,hV.inter hA.isOpen_compl,⟨huV,huA⟩,?_,?_⟩
  · exact Set.disjoint_left.mpr (fun x hx hxA => hx.2 hxA)
  · intro x hx
    constructor
    · rintro (hxA | ⟨t,ht,hxt⟩)
      · exact False.elim (hx.2 hxA)
      · exact ⟨t,hxt⟩
    · intro hxJ
      have him : x ∈ J '' Set.Ioo R T := by rw [himage]; exact ⟨hx.1,hxJ⟩
      obtain ⟨t,ht,hxt⟩ := him
      exact Or.inr ⟨t,⟨ht.1.le,ht.2.le⟩,hxt⟩
private theorem actual_short_source_return_has_interior_target_period_contact
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (a b : Curve X) (F J : ℝ → H2) (g : G)
    (hF : ∀ x : ℝ, q (F x)=a.map (Circle.exp x))
    (hJ : ∀ x : ℝ, q (J x)=b.map (Circle.exp x))
    (hJperiod : ∀ x : ℝ, J (x+2*Real.pi)=g • J x)
    (r s t v : ℝ) (k : G) (hrs : r<s) (hshort : s-r<2*Real.pi)
    (htv : t≠v) (hr : F r=k • J t) (hs : F s=k • J v)
    (hwide : 2*Real.pi≤|v-t|) :
    ∃ n : ℤ, ∃ θ : ℝ, (n=1 ∨ n = -1) ∧ θ ∈ Set.uIoo t v ∧
      θ=t+n*(2*Real.pi) ∧ k • J θ=(k*g^n*k⁻¹) • F r := by
  have hqdiff : q (F r)≠q (F s) := by
    intro he
    have hcircle : Circle.exp r=Circle.exp s := a.embedded.injective (by simpa only [hF] using he)
    have hrs' := Circle.exp_injOn_Icc hshort ⟨le_rfl,hrs.le⟩ ⟨hrs.le,le_rfl⟩ hcircle
    exact hrs.ne hrs'
  have htargetdiff : Circle.exp t≠Circle.exp v := by
    intro he
    apply hqdiff
    rw [hr,hs,hq.map_smul,hq.map_smul,hJ,hJ,he]
  have hgapne : |v-t|≠2*Real.pi := by
    intro he
    apply htargetdiff
    by_cases hle : t≤v
    · rw [abs_of_nonneg (sub_nonneg.mpr hle)] at he
      apply Circle.exp_eq_exp.mpr
      refine ⟨(-1 : ℤ),?_⟩
      norm_num
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hle))] at he
      apply Circle.exp_eq_exp.mpr
      refine ⟨(1 : ℤ),?_⟩
      norm_num
      linarith
  have hstrict : 2*Real.pi < |v-t| := lt_of_le_of_ne hwide (Ne.symm hgapne)
  have hint := (reused_curve_lift_integer_period_and_stabilizer q hq id b J g hJ hJperiod).1
  have hpoint (n : ℤ) : k • J (t+n*(2*Real.pi))=(k*g^n*k⁻¹) • F r := by
    rw [hint,hr,mul_smul,mul_smul,inv_smul_smul]
  rcases lt_or_gt_of_ne htv with htv | hvt
  · rw [abs_of_nonneg (sub_nonneg.mpr htv.le)] at hstrict
    refine ⟨1,t+2*Real.pi,Or.inl rfl,?_,by norm_num,?_⟩
    · rw [Set.uIoo_of_le htv.le]
      constructor <;> linarith [Real.pi_pos]
    · simpa using hpoint 1
  · rw [abs_of_nonpos (sub_nonpos.mpr hvt.le)] at hstrict
    refine ⟨-1,t-2*Real.pi,Or.inr rfl,?_,by norm_num; ring,?_⟩
    · rw [Set.uIoo_of_ge hvt.le]
      constructor <;> linarith [Real.pi_pos]
    · simpa [sub_eq_add_neg] using hpoint (-1)


private theorem actual_clean_return_target_wide_constructs_smaller_return
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
    (q : H2 → X) (hq : IsQuotientCoveringMap q G)
    (hdeck : ∀ k : G, Isometry (fun z : H2 => k • z))
    (a b : Curve X) (ht : Transverse a b)
    (hcount : 2 ≤ (a.image ∩ b.image).ncard)
    (F J : C(ℝ,H2)) (g : G)
    (hinjF : Function.Injective F) (hinjJ : Function.Injective J)
    (hproperF : IsProperMap F) (hproperJ : IsProperMap J)
    (hF : ∀ u, q (F u)=a.map (Circle.exp u))
    (hJ : ∀ u, q (J u)=b.map (Circle.exp u))
    (hFperiod : ∀ u, F (u+2*Real.pi)=g • F u)
    (hJperiod : ∀ u, J (u+2*Real.pi)=g • J u)
    (r s t v : ℝ) (k : G) (hrs : r<s) (hshort : s-r<2*Real.pi)
    (htv : t≠v) (hr : F r=k • J t) (hs : F s=k • J v)
    (hclean : ∀ u ∈ Set.Ioo r s, q (F u) ∉ b.image)
    (hwide : 2*Real.pi≤|v-t|) :
    ∃ x y τ υ : ℝ, x<y ∧ y-x<2*Real.pi ∧ ∃ l : G,
      F x=l • J τ ∧ F y=l • J υ ∧
      (∀ u ∈ Set.Ioo x y, q (F u) ∉ b.image) ∧ |υ-τ| < |v-t| := by
  classical
  let e := hyperbolicPlaneHomeomorph
  let deckHomeo (m : G) : H2 ≃ₜ H2 :=
    { toEquiv :=
        { toFun := fun z => m • z
          invFun := fun z => m⁻¹ • z
          left_inv := fun z => by simp
          right_inv := fun z => by simp }
      continuous_toFun := (hdeck m).continuous
      continuous_invFun := (hdeck m⁻¹).continuous }
  let Jk : C(ℝ,H2) := ⟨fun u => k • J u,(hdeck k).continuous.comp J.continuous⟩
  have hJkinj : Function.Injective Jk := (MulAction.injective k).comp hinjJ
  have hJkproper : IsProperMap Jk := (deckHomeo k).isProperMap.comp hproperJ
  have hJkembed : IsEmbedding Jk := (IsClosedEmbedding.of_continuous_injective_isClosedMap
    Jk.continuous hJkinj hJkproper.isClosedMap).isEmbedding
  let A : Set H2 := F '' Set.Icc r s
  let B : Set H2 := Jk '' Set.uIcc t v
  let L := A ∪ B
  let C : Set Plane := (e ∘ F) '' Set.Icc r s ∪ (e ∘ Jk) '' Set.uIcc t v
  have hAL : IsCompact A := isCompact_Icc.image F.continuous
  have hpre : e ⁻¹' C=L := by
    dsimp [C,L,A,B]
    rw [Set.image_comp,Set.image_comp,
      Set.preimage_image_eq _ e.injective,Set.preimage_image_eq _ e.injective]
  let U : Set H2 := e ⁻¹' inside C
  let V : Set H2 := e ⁻¹' outside C
  let K : Set H2 := e ⁻¹' closure (inside C)
  let Fp : C(ℝ,Plane) := ⟨e ∘ F,e.continuous.comp F.continuous⟩
  let Jp : C(ℝ,Plane) := ⟨e ∘ Jk,e.continuous.comp Jk.continuous⟩
  have hcleanp : ∀ u ∈ Set.Ioo r s, Fp u ∉ Set.range Jp := by
    intro u hu ⟨w,hw⟩
    have he : k • J w=F u := e.injective hw
    apply hclean u hu
    rw [←he,hq.map_smul,hJ]
    exact Set.mem_range_self _
  have hC : IsJordanCurve C := by
    have hh := clean_embedded_lift_pair_is_jordan_boundary Fp Jp
      (e.injective.comp hinjF) (e.injective.comp hJkinj) r s t v hrs htv
      (congrArg e hr) (congrArg e hs) hcleanp
    rw [parametrized_segment_image_eq_unordered_interval_image Fp r s,
      parametrized_segment_image_eq_unordered_interval_image Jp v t,
      Set.uIcc_of_le hrs.le,Set.uIcc_comm v t] at hh
    exact hh
  have hsep := jordan_curve_theorem hC
  have hU : IsOpen U := hsep.isOpen_inside.preimage e.continuous
  have hV : IsOpen V := hsep.isOpen_outside.preimage e.continuous
  have hdisUV : Disjoint U V := disjoint_inside_outside.preimage e
  have hcover : U ∪ V=Lᶜ := by
    rw [←Set.preimage_union,inside_union_outside,Set.preimage_compl,hpre]
  have hfrontU : frontier U=L := by rw [←e.preimage_frontier,hsep.frontier_inside,hpre]
  have hfrontV : frontier V=L := by rw [←e.preimage_frontier,hsep.frontier_outside,hpre]
  have hK : IsCompact K := e.isProperMap.isCompact_preimage
    (Metric.isCompact_of_isClosed_isBounded isClosed_closure hsep.isBounded_inside.closure)
  have hUK : U ⊆ K := fun z hz => subset_closure hz
  have hdisUL : Disjoint U L := by
    apply Set.disjoint_left.mpr
    intro z hz hzL
    exact inside_subset_compl hz (show e z ∈ C from by rw [←hpre] at hzL; exact hzL)
  have hUclean : ∀ z ∈ U, q z ∉ b.image := by
    exact actual_clean_lift_bigon_inside_avoids_projected_target q hq hdeck b F J g
      hinjF hinjJ hproperJ hJ hJperiod r s t v k hrs htv hr hs hclean
  obtain ⟨n,θ,hn,hθ,hθeq,hθpoint⟩ := actual_short_source_return_has_interior_target_period_contact
    q hq a b F J g hF hJ hJperiod r s t v k hrs hshort htv hr hs hwide
  let m : G := k*g^n*k⁻¹
  let M : C(ℝ,H2) := ⟨fun u => m • F u,(hdeck m).continuous.comp F.continuous⟩
  have hMproper : IsProperMap M := (deckHomeo m).isProperMap.comp hproperF
  have hMinj : Function.Injective M := (MulAction.injective m).comp hinjF
  have hMproj : ∀ u, q (M u)=a.map (Circle.exp u) := by
    intro u
    change q (m • F u)=_
    rw [hq.map_smul,hF]
  have hpin : M r=Jk θ := hθpoint.symm
  have hθA : Jk θ ∉ A := by
    rintro ⟨u,hu,hue⟩
    have hub : q (F u) ∈ b.image := by
      rw [hue]
      change q (k • J θ) ∈ b.image
      rw [hq.map_smul,hJ]
      exact Set.mem_range_self _
    by_cases hur : u=r
    · have he : t=θ := hJkinj (hr.symm.trans (hur ▸ hue))
      rw [←he] at hθ
      exact Set.left_notMem_uIoo hθ
    by_cases hus : u=s
    · have he : v=θ := hJkinj (hs.symm.trans (hus ▸ hue))
      rw [←he] at hθ
      exact Set.right_notMem_uIoo hθ
    exact hclean u ⟨lt_of_le_of_ne hu.1 (Ne.symm hur),lt_of_le_of_ne hu.2 hus⟩ hub
  obtain ⟨W,hW,hθW,_,hlocal⟩ := embedded_target_segment_is_local_full_boundary
    Jk hJkembed A hAL.isClosed (min t v) (max t v) θ hθ hθA
  have hlocal' : ∀ z ∈ W, z ∈ L ↔ z ∈ Set.range (fun u : ℝ => k • J u) := hlocal
  obtain ⟨x,y,hxy,hxL,hyL,hpinned,hinside⟩ :=
    actual_transverse_local_boundary_has_pinned_inside_component q hq hdeck a b ht M J g
      hMinj hMproper hMproj hJ hJperiod k r ⟨θ,hpin.symm⟩ L U V K W
      hU hV hdisUV hcover hfrontU hfrontV hK hUK hW (hpin.symm ▸ hθW) hlocal'
  have hrB : F r ∈ B := ⟨t,Set.left_mem_uIcc,hr.symm⟩
  have hsB : F s ∈ B := ⟨v,Set.right_mem_uIcc,hs.symm⟩
  have hends := actual_deck_source_first_exit_endpoints_on_target q hq a F g m hinjF hF hFperiod
    U B r s x y hrs hxy hdisUL hxL hyL hrB hsB hinside
  obtain ⟨τ,υ,hτ,hυ,hx,hy,hgap⟩ := pinned_target_segment_endpoints_have_smaller_gap
    Jk M hJkinj t v θ r x y hθ hpin hpinned hends.1 hends.2
  have hnewclean : ∀ u ∈ Set.Ioo x y, q (F u) ∉ b.image := by
    intro u hu
    have hh := hUclean (M u) (hinside u hu)
    simpa only [M,ContinuousMap.coe_mk,hq.map_smul] using hh
  have hnewshort := clean_actual_curve_interval_short a b ht.1 hcount x y
    (by simpa only [hF] using hnewclean)
  refine ⟨x,y,τ,υ,hxy,hnewshort,m⁻¹*k,?_,?_,hnewclean,hgap⟩
  · have hh := congrArg (fun z : H2 => m⁻¹ • z) hx
    simpa only [M,Jk,ContinuousMap.coe_mk,inv_smul_smul,smul_smul,inv_mul_cancel,one_smul] using hh
  · have hh := congrArg (fun z : H2 => m⁻¹ • z) hy
    simpa only [M,Jk,ContinuousMap.coe_mk,inv_smul_smul,smul_smul,inv_mul_cancel,one_smul] using hh
end CurveComplex.Hyperbolic

namespace CurveComplex.Hyperbolic
open Set Topology
/-- Pure actual-cover contact selection. The endpoint lines are arbitrary
continuous embedded-curve lifts, never assumed geodesic or isometric.
The uniform bound belongs to the literal common period deck action. -/
theorem periodic_actual_h2_lifts_have_clean_matched_contacts
    {X G : Type} [TopologicalSpace X] [Group G] [MulAction G H2]
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
    ∃ r s t v : ℝ, r < s ∧ s-r < 2*Real.pi ∧ t ≠ v ∧
      |v-t| < 2*Real.pi ∧ ∃ k : G,
      F r = k • J t ∧ F s = k • J v ∧
      ∀ x ∈ Set.Ioo r s, q (F x) ∉ b.image := by
  classical
  have hFp := actual_uniform_displacement_periodic_lift_closed_embedding q a F g
    (hdeck g) ε hε hdisplacement hF hFperiod
  have hJp := actual_uniform_displacement_periodic_lift_closed_embedding q b J g
    (hdeck g) ε hε hdisplacement hJ hJperiod
  obtain ⟨r,s,t,v,k,hrs,hshort,htv,hr,hs,hclean,hmin⟩ :=
    actual_periodic_h2_clean_return_minimizes_target_gap q hq hdeck a b ht hcount F J g
      ε hε hdisplacement hF hJ hFperiod hJperiod
  have htargetshort : |v-t| < 2*Real.pi := by
    by_contra hwide
    obtain ⟨x,y,τ,υ,hxy,hnewshort,l,hx,hy,hnewclean,hgap⟩ :=
      actual_clean_return_target_wide_constructs_smaller_return q hq hdeck a b ht hcount F J g
        hFp.2.injective hJp.2.injective hFp.1 hJp.1 hF hJ hFperiod hJperiod
        r s t v k hrs hshort htv hr hs hclean (le_of_not_gt hwide)
    exact (not_lt_of_ge (hmin x y τ υ l hxy hnewshort hx hy hnewclean)) hgap
  exact ⟨r,s,t,v,hrs,hshort,htv,htargetshort,k,hr,hs,hclean⟩


end CurveComplex.Hyperbolic
