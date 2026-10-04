import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
open Set Schoenflies Topology
namespace CurveComplex

-- Signed corner connector: includes BOTH genuine entering-arm directions.
-- No assumption that the entering original-g arm lies above the selected axis.
theorem actual_signed_corner_segment_counts {J : Type*} (a b : J → Plane)
    (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
    (δ ξ h : ℝ) (hδ : 0 < δ) (hh : h ≠ 0) :
    ∀ j, (segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∩
      (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).Finite ∧
      (segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∩
      (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).ncard ≤ 1 := by
  let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h)
  have hline (z : Plane) (hz : z ∈ C) : h*z 0-(ξ+δ)*z 1 = -δ*h := by
    change z ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) at hz
    rw [segment_eq_image'] at hz
    obtain ⟨t,ht,rfl⟩ := hz
    change h*(-δ+t*(ξ- -δ))-(ξ+δ)*(0+t*(h-0)) = -δ*h
    ring
  have hsingle (v : Plane) : (C ∩ segment ℝ (0 : Plane) v).Subsingleton := by
    intro x hx y hy
    rw [segment_eq_image'] at hx hy
    obtain ⟨t,ht,he⟩ := hx.2
    obtain ⟨s,hs,hse⟩ := hy.2
    let L := h*v 0-(ξ+δ)*v 1
    have htL : t*L = -δ*h := by
      have hl := hline x hx.1
      rw [← he] at hl
      change h*(0+t*(v 0-0))-(ξ+δ)*(0+t*(v 1-0)) = -δ*h at hl
      dsimp [L]
      nlinarith [hl]
    have hsL : s*L = -δ*h := by
      have hl := hline y hy.1
      rw [← hse] at hl
      change h*(0+s*(v 0-0))-(ξ+δ)*(0+s*(v 1-0)) = -δ*h at hl
      dsimp [L]
      nlinarith [hl]
    have hL : L ≠ 0 := by
      intro heL
      rw [heL,mul_zero] at htL
      have hz := (mul_eq_zero.mp htL.symm).resolve_right hh
      linarith
    have hts := mul_right_cancel₀ hL (htL.trans hsL.symm)
    exact he.symm.trans (hts ▸ hse)
  have havoid (v : Plane) (hv : h*v 1 < 0) : Disjoint C (segment ℝ (0 : Plane) v) := by
    apply Set.disjoint_left.mpr
    intro z hz hzv
    change z ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) at hz
    rw [segment_eq_image'] at hz hzv
    obtain ⟨t,ht,he⟩ := hz
    obtain ⟨s,hs,hse⟩ := hzv
    have hzy := congrArg (fun q : Plane => q 1) he
    have hsy := congrArg (fun q : Plane => q 1) hse
    change 0+t*(h-0) = z 1 at hzy
    change 0+s*(v 1-0) = z 1 at hsy
    have hs0 : s = 0 := by
      by_contra hne
      have hsp : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hne)
      have hneg := mul_neg_of_pos_of_neg hsp hv
      have hpos := mul_nonneg ht.1 (mul_self_nonneg h)
      have hrel := congrArg (fun x : ℝ => h*x) (hzy.trans hsy.symm)
      nlinarith [hrel]
    have ht0 : t = 0 := (mul_eq_zero.mp (by simpa [hs0] using hzy.trans hsy.symm)).resolve_right hh
    have hz0 : z = 0 := by rw [hs0] at hse; simpa using hse.symm
    have hzx := congrArg (fun q : Plane => q 0) he
    rw [hz0,ht0] at hzx
    change -δ+0*(ξ- -δ) = 0 at hzx
    linarith
  intro j
  rcases lt_or_gt_of_ne hh with hn | hp
  · have hd := havoid (a j) (mul_neg_of_neg_of_pos hn (ha j))
    have heq : C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) =
        C ∩ segment ℝ (0 : Plane) (b j) := by
      rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp hd,Set.empty_union]
    change (C ∩ _).Finite ∧ (C ∩ _).ncard ≤ 1
    rw [heq]
    exact ⟨(hsingle (b j)).finite,(Set.ncard_le_one (hsingle (b j)).finite).mpr (hsingle (b j))⟩
  · have hd := havoid (b j) (mul_neg_of_pos_of_neg hp (hb j))
    have heq : C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) =
        C ∩ segment ℝ (0 : Plane) (a j) := by
      rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp hd,Set.union_empty]
    change (C ∩ _).Finite ∧ (C ∩ _).ncard ≤ 1
    rw [heq]
    exact ⟨(hsingle (a j)).finite,(Set.ncard_le_one (hsingle (a j)).finite).mpr (hsingle (a j))⟩

-- The corner endpoint approaches the REAL entering original-g ray from the
-- sector containing the exterior selected arm. Both vertical sign cases survive.
theorem actual_near_entering_ray_corner_avoid
    (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε)
    (q v w : Plane) (hq : q ∈ segment ℝ (0 : Plane) v)
    (hqy : q 1 ≠ 0) (hvw : v 1*w 1 < 0) :
    Disjoint (segment ℝ (Plane.mk (-δ) 0) (Plane.mk (q 0-ε) (q 1)))
      (segment ℝ (0 : Plane) v ∪ segment ℝ (0 : Plane) w) := by
  let C := segment ℝ (Plane.mk (-δ) 0) (Plane.mk (q 0-ε) (q 1))
  obtain ⟨a,ha,hea⟩ := (segment_eq_image' ℝ (0 : Plane) v) ▸ hq
  have heay := congrArg (fun x : Plane => x 1) hea
  change 0+a*(v 1-0) = q 1 at heay
  have heav := congrArg (fun x : Plane => x 0) hea
  change 0+a*(v 0-0) = q 0 at heav
  have hapos : 0 < a := lt_of_le_of_ne ha.1 (by
    intro he
    apply hqy
    rw [← heay,← he]
    simp)
  have hvne : v 1 ≠ 0 := (mul_ne_zero_iff.mp (ne_of_lt hvw)).1
  have hchosen : Disjoint C (segment ℝ (0 : Plane) v) := by
    apply Set.disjoint_left.mpr
    intro z hz hzv
    change z ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk (q 0-ε) (q 1)) at hz
    rw [segment_eq_image'] at hz hzv
    obtain ⟨t,ht,het⟩ := hz
    obtain ⟨b,hb,heb⟩ := hzv
    have hx := congrArg (fun x : Plane => x 0) het
    have hy := congrArg (fun x : Plane => x 1) het
    have hbx := congrArg (fun x : Plane => x 0) heb
    have hby := congrArg (fun x : Plane => x 1) heb
    change -δ+t*(q 0-ε- -δ) = z 0 at hx
    change 0+t*(q 1-0) = z 1 at hy
    change 0+b*(v 0-0) = z 0 at hbx
    change 0+b*(v 1-0) = z 1 at hby
    have hscale : (1-t)*δ+t*ε > 0 := by
      nlinarith [ht.1,ht.2,
        mul_nonneg (sub_nonneg.mpr ht.2) hδ.le,mul_nonneg ht.1 hε.le]
    have hdet : ((1-t)*δ+t*ε)*v 1 = 0 := by
      have heq := congrArg (fun x : ℝ => v 1*x) (hx.trans hbx.symm)
      have heq' := congrArg (fun x : ℝ => v 0*x) (hy.trans hby.symm)
      have heq'' := congrArg (fun x : ℝ => t*x) (heav.trans (by rfl))
      have hqdet : q 0*v 1-q 1*v 0 = 0 := by rw [← heav,← heay]; ring
      have hqdetT := congrArg (fun x : ℝ => t*x) hqdet
      nlinarith [heq,heq',hqdetT]
    exact (mul_ne_zero (ne_of_gt hscale) hvne) hdet
  have hother : Disjoint C (segment ℝ (0 : Plane) w) := by
    apply Set.disjoint_left.mpr
    intro z hz hzw
    change z ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk (q 0-ε) (q 1)) at hz
    rw [segment_eq_image'] at hz hzw
    obtain ⟨t,ht,het⟩ := hz
    obtain ⟨b,hb,heb⟩ := hzw
    have hy := congrArg (fun x : Plane => x 1) het
    have hby := congrArg (fun x : Plane => x 1) heb
    change 0+t*(q 1-0) = z 1 at hy
    change 0+b*(w 1-0) = z 1 at hby
    have hsign : q 1*w 1 < 0 := by
      rw [← heay]
      have := mul_neg_of_pos_of_neg hapos hvw
      nlinarith
    have hb0 : b = 0 := by
      by_contra hn
      have hbp : 0 < b := lt_of_le_of_ne hb.1 (Ne.symm hn)
      have hneg := mul_neg_of_pos_of_neg hbp hsign
      have hnn := mul_nonneg ht.1 (mul_self_nonneg (q 1))
      have heq := congrArg (fun x : ℝ => q 1*x) (hy.trans hby.symm)
      nlinarith [heq]
    have ht0 : t = 0 := (mul_eq_zero.mp (by simpa [hb0] using hy.trans hby.symm)).resolve_right hqy
    have hx := congrArg (fun x : Plane => x 0) het
    have hbx := congrArg (fun x : Plane => x 0) heb
    change -δ+t*(q 0-ε- -δ) = z 0 at hx
    change 0+b*(w 0-0) = z 0 at hbx
    rw [ht0] at hx
    rw [hb0] at hbx
    simp only [zero_mul,add_zero] at hx hbx
    linarith
  exact Set.disjoint_union_right.mpr ⟨hchosen,hother⟩

-- An open neighborhood of the genuine side germ supplies a continuous family
-- of off-side endpoints. No clearance assumption about a fabricated endpoint.
theorem actual_near_entering_ray_corner_family
    (δ η : ℝ) (hδ : 0 < δ)
    (q v w : Plane) (hq : q ∈ segment ℝ (0 : Plane) v)
    (hqy : q 1 ≠ 0) (hvw : v 1*w 1 < 0)
    (O : Set Plane) (hO : IsOpen O) (hqO : q ∈ O)
    (hstart : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η)
    (hqball : q ∈ Metric.ball (0 : Plane) η) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      let endpoint := Plane.mk (q 0-ε) (q 1)
      let C := segment ℝ (Plane.mk (-δ) 0) endpoint
      endpoint ∈ O ∧ C ⊆ Metric.ball (0 : Plane) η ∧
        Disjoint C (segment ℝ (0 : Plane) v ∪ segment ℝ (0 : Plane) w) := by
  let endpoint : ℝ → Plane := fun ε => Plane.mk (q 0-ε) (q 1)
  have hcont : Continuous endpoint := by fun_prop
  have hzero : endpoint 0 = q := by ext i; fin_cases i <;> simp [endpoint,Plane.mk]
  have hopen : IsOpen (endpoint ⁻¹' (O ∩ Metric.ball (0 : Plane) η)) :=
    (hO.inter Metric.isOpen_ball).preimage hcont
  have hmem : (0 : ℝ) ∈ endpoint ⁻¹' (O ∩ Metric.ball (0 : Plane) η) := by
    change endpoint 0 ∈ O ∩ Metric.ball (0 : Plane) η
    rw [hzero]
    exact ⟨hqO,hqball⟩
  obtain ⟨ε₀,hε₀,hball⟩ := Metric.isOpen_iff.mp hopen 0 hmem
  refine ⟨ε₀,hε₀,?_⟩
  intro ε hε hεsmall
  have hep := hball (show ε ∈ Metric.ball (0 : ℝ) ε₀ by
    simpa [Real.dist_eq,abs_of_pos hε] using hεsmall)
  exact ⟨hep.1,(convex_ball (0 : Plane) η).segment_subset hstart hep.2,
    actual_near_entering_ray_corner_avoid δ ε hδ hε q v w hq hqy hvw⟩

theorem actual_signed_chart_connector_arc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (F : OpenPartialHomeomorph S Plane) (δ ξ h : ℝ) (hh : h ≠ 0)
    (hTarget : segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ⊆ F.target) :
    ∃ f : C(Interval,S), Topology.IsEmbedding f ∧
      Set.range f = F.symm '' segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ∧
      f 0 = F.symm (Plane.mk (-δ) 0) ∧ f 1 = F.symm (Plane.mk ξ h) ∧
      (∀ t, f t ∈ F.source ∧ F (f t) = Plane.mk (-δ+t.val*(ξ+δ)) (h*t.val)) := by
  let γ : Interval → Plane := fun t => Plane.mk (-δ+t.val*(ξ+δ)) (h*t.val)
  have hγ : Continuous γ := by fun_prop
  have hγSeg (t : Interval) : γ t ∈ segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) := by
    rw [segment_eq_image']
    refine ⟨t.val,t.property,?_⟩
    ext i
    fin_cases i <;> simp [γ,Plane.mk,mul_comm,sub_neg_eq_add]
  let f : C(Interval,S) := ⟨fun t => F.symm (γ t),
    F.symm.continuousOn.comp_continuous hγ (fun t => hTarget (hγSeg t))⟩
  have hinj : Function.Injective f := by
    intro t s he
    have hg : γ t = γ s := F.symm.injOn (hTarget (hγSeg t)) (hTarget (hγSeg s)) he
    have hv := congrArg (fun z : Plane => z 1) hg
    change h*t.val = h*s.val at hv
    exact Subtype.ext (mul_left_cancel₀ hh hv)
  refine ⟨f,(f.continuous.isClosedEmbedding hinj).isEmbedding,?_,?_,?_,?_⟩
  · ext x
    constructor
    · rintro ⟨t,rfl⟩
      exact ⟨γ t,hγSeg t,rfl⟩
    · rintro ⟨y,hy,rfl⟩
      rw [segment_eq_image'] at hy
      obtain ⟨t,ht,he⟩ := hy
      refine ⟨⟨t,ht⟩,?_⟩
      apply congrArg F.symm
      change Plane.mk (-δ+t*(ξ+δ)) (h*t) = y
      rw [← he]
      ext i
      fin_cases i <;> simp [Plane.mk,mul_comm,sub_neg_eq_add]
  · change F.symm (γ 0) = F.symm (Plane.mk (-δ) 0)
    apply congrArg F.symm
    ext i
    fin_cases i <;> simp [γ]
  · change F.symm (γ 1) = F.symm (Plane.mk ξ h)
    apply congrArg F.symm
    ext i
    fin_cases i <;> simp [γ]
  · intro t
    exact ⟨F.map_target (hTarget (hγSeg t)),F.right_inv (hTarget (hγSeg t))⟩

theorem actual_signed_chart_connector_selected_meet
    {S : Type*} [TopologicalSpace S]
    (c : Curve S) (F : OpenPartialHomeomorph S Plane) (δ ξ h ρ : ℝ)
    (hh : h ≠ 0) (arc : C(Interval,S))
    (hrange : Set.range arc = F.symm '' segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h))
    (hstart : arc 0 = F.symm (Plane.mk (-δ) 0)) (hstartc : arc 0 ∈ c.image)
    (hcore : segment ℝ (Plane.mk (-δ) 0) (Plane.mk ξ h) ⊆ F.target ∩ Metric.ball (0 : Plane) ρ)
    (haxis : ∀ x ∈ F.source, ‖F x‖ < ρ → (x ∈ c.image ↔ F x 1 = 0)) :
    Set.range arc ∩ c.image = {arc 0} := by
  ext x
  constructor
  · rintro ⟨hx,hxc⟩
    rw [hrange] at hx
    obtain ⟨q,hq,rfl⟩ := hx
    have hqs := F.map_target (hcore hq).1
    have hqn : ‖F (F.symm q)‖ < ρ := by
      rw [F.right_inv (hcore hq).1]
      simpa only [Metric.mem_ball,dist_zero_right] using (hcore hq).2
    have hq0 := (haxis (F.symm q) hqs hqn).mp hxc
    rw [F.right_inv (hcore hq).1] at hq0
    rw [segment_eq_image'] at hq
    obtain ⟨t,ht,he⟩ := hq
    have hy := congrArg (fun z : Plane => z 1) he
    change 0+t*(h-0) = q 1 at hy
    have ht0 : t = 0 := (mul_eq_zero.mp (by simpa [hq0] using hy)).resolve_right hh
    have heq : q = Plane.mk (-δ) 0 := by
      rw [ht0] at he
      simpa using he.symm
    rw [heq,← hstart]
    exact Set.mem_singleton _
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact ⟨⟨0,rfl⟩,hstartc⟩

-- Restrict an approaching connector endpoint to a genuine common chart.
theorem actual_corner_endpoint_common_chart_family
    {S : Type*} [TopologicalSpace S]
    (F E : OpenPartialHomeomorph S Plane) (q : S)
    (hqF : q ∈ F.source) (hqE : q ∈ E.source) (bound : ℝ) (hbound : 0 < bound) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < bound ∧
      ∃ endpoint : C(Interval,S), endpoint 0 = q ∧
        (∀ t, endpoint t ∈ F.source ∧ endpoint t ∈ E.source ∧
          endpoint t = F.symm (Plane.mk (F q 0-ρ*t.val) (F q 1))) := by
  let P : Set Plane := F '' (F.source ∩ E.source)
  have hP : IsOpen P := F.isOpen_image_source_inter E.open_source
  let v : ℝ → Plane := fun ε => Plane.mk (F q 0-ε) (F q 1)
  have hv : Continuous v := by fun_prop
  have hv0 : v 0 = F q := by ext i; fin_cases i <;> simp [v]
  have hvP : (0 : ℝ) ∈ v ⁻¹' P := by
    change v 0 ∈ P
    rw [hv0]
    exact ⟨q,⟨hqF,hqE⟩,rfl⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp (hP.preimage hv) 0 hvP
  let ρ := min r bound/2
  have hρ : 0 < ρ := half_pos (lt_min hr hbound)
  have hρr : ρ < r := by dsimp [ρ]; have := min_le_left r bound; linarith
  have hρb : ρ < bound := by dsimp [ρ]; have := min_le_right r bound; linarith
  have hpoint (t : Interval) : v (ρ*t.val) ∈ P := hball (by
    change dist (ρ*t.val) (0 : ℝ) < r
    rw [Real.dist_eq,sub_zero,abs_of_nonneg (mul_nonneg hρ.le t.property.1)]
    nlinarith [t.property.2])
  have htarg (t : Interval) : v (ρ*t.val) ∈ F.target := by
    obtain ⟨x,hx,he⟩ := hpoint t
    rw [← he]
    exact F.map_source hx.1
  let endpoint : C(Interval,S) := ⟨fun t => F.symm (v (ρ*t.val)),
    F.symm.continuousOn.comp_continuous (hv.comp (by fun_prop)) htarg⟩
  refine ⟨ρ,hρ,hρb,endpoint,?_,?_⟩
  · change F.symm (v (ρ*0)) = q
    rw [mul_zero,hv0,F.left_inv hqF]
  · intro t
    obtain ⟨x,hx,he⟩ := hpoint t
    have heq : endpoint t = x := by
      change F.symm (v (ρ*t.val)) = x
      rw [← he,F.left_inv hx.1]
    exact ⟨heq.symm ▸ hx.1,heq.symm ▸ hx.2,rfl⟩

theorem actual_continuous_positive_parameter_sign
    (y : C(Interval,ℝ)) (hzero : ∀ t : Interval, 0 < t.val → y t ≠ 0) :
    ∃ σ : ℝ, (σ = -1 ∨ σ = 1) ∧ ∀ t : Interval, 0 < t.val → 0 < σ*y t := by
  have hconn : IsPreconnected (y '' Set.Ioi (0 : Interval)) :=
    isPreconnected_Ioi.image y y.continuous.continuousOn
  have hcover : y '' Set.Ioi (0 : Interval) ⊆ Set.Iio (0 : ℝ) ∪ Set.Ioi 0 := by
    rintro x ⟨t,ht,rfl⟩
    exact lt_or_gt_of_ne (hzero t ht)
  have hdis : Disjoint (Set.Iio (0 : ℝ)) (Set.Ioi 0) :=
    Set.disjoint_left.mpr (by
      intro x hx hy
      change x < 0 at hx
      change 0 < x at hy
      linarith)
  rcases hconn.subset_or_subset isOpen_Iio isOpen_Ioi hdis hcover with hn | hp
  · refine ⟨-1,Or.inl rfl,?_⟩
    intro t ht
    have hneg := hn ⟨t,ht,rfl⟩
    change y t < 0 at hneg
    simpa using neg_pos.mpr hneg
  · refine ⟨1,Or.inr rfl,?_⟩
    intro t ht
    have hpos := hp ⟨t,ht,rfl⟩
    change 0 < y t at hpos
    simpa using hpos

-- The original boundary prefix, including all its real parameters, belongs
-- to the actual corner neighborhood. This will locate the first/last events.
theorem actual_original_corner_angular_prefix
    {S : Type*} [TopologicalSpace S]
    (c : Curve S) (b q : Circle) (a z ε : ℝ) (hε : 0 < ε)
    (τ : Interval) (side : Bool) (U : Set S)
    (hq : c.map q = c.map (b*Circle.exp (if side then a else z)))
    (hU : ∀ t : Interval, c.map (q*Circle.exp (if side then ε*t.val else -(ε*t.val))) ∈ U) :
    ∀ θ : ℝ, θ ∈ (if side then Set.Ioc a (a+ε*τ.val) else Set.Ico (z-ε*τ.val) z) →
      c.map (b*Circle.exp θ) ∈ U := by
  have hqeq := c.embedded.injective hq
  cases side
  · change q = b*Circle.exp z at hqeq
    intro θ hθ
    change z-ε*τ.val ≤ θ ∧ θ < z at hθ
    let t : Interval := ⟨(z-θ)/ε,⟨div_nonneg (by linarith only [hθ.2]) hε.le,
      (div_le_one hε).mpr (by nlinarith [hθ.1,τ.property.2])⟩⟩
    have hεt : ε*t.val = z-θ := by dsimp [t]; exact mul_div_cancel₀ _ (ne_of_gt hε)
    have hm := hU t
    rw [hqeq] at hm
    change c.map ((b*Circle.exp z)*Circle.exp (-(ε*t.val))) ∈ U at hm
    have he : b*Circle.exp θ = (b*Circle.exp z)*Circle.exp (-(ε*t.val)) := by
      rw [hεt,mul_assoc,← Circle.exp_add]
      congr 1
      congr 1
      ring
    rwa [← he] at hm
  · change q = b*Circle.exp a at hqeq
    intro θ hθ
    change a < θ ∧ θ ≤ a+ε*τ.val at hθ
    let t : Interval := ⟨(θ-a)/ε,⟨div_nonneg (by linarith only [hθ.1]) hε.le,
      (div_le_one hε).mpr (by nlinarith [hθ.2,τ.property.2])⟩⟩
    have hεt : ε*t.val = θ-a := by dsimp [t]; exact mul_div_cancel₀ _ (ne_of_gt hε)
    have hm := hU t
    rw [hqeq] at hm
    change c.map ((b*Circle.exp a)*Circle.exp (ε*t.val)) ∈ U at hm
    have he : b*Circle.exp θ = (b*Circle.exp a)*Circle.exp (ε*t.val) := by
      rw [hεt,mul_assoc,← Circle.exp_add]
      congr 1
      congr 1
      ring
    rwa [← he] at hm

theorem actual_original_corner_entering_parameter
    {S : Type*} [TopologicalSpace S] [DecidableEq S]
    (c : Curve S) (b q : Circle) (a z h : ℝ) (hh : 0 < h) (hshort : h < z-a)
    (p : S) (hq : c.map q = p)
    (hp : p = c.map (b*Circle.exp a) ∨ p = c.map (b*Circle.exp z)) :
    let side := decide (p = c.map (b*Circle.exp a))
    let θ := if side then a+h else z-h
    θ ∈ Set.Ioo a z ∧ c.map (b*Circle.exp θ) =
      c.map (q*Circle.exp (if side then h else -h)) := by
  classical
  by_cases hpa : p = c.map (b*Circle.exp a)
  · have hqeq : q = b*Circle.exp a := c.embedded.injective (hq.trans hpa)
    simp only [hpa,decide_true,ite_true]
    refine ⟨⟨by linarith only [hh],by linarith only [hshort]⟩,?_⟩
    rw [hqeq,Circle.exp_add]
    simp only [mul_assoc]
  · have hpz : p = c.map (b*Circle.exp z) := hp.resolve_left hpa
    have hqeq : q = b*Circle.exp z := c.embedded.injective (hq.trans hpz)
    simp only [hpa,decide_false,Bool.false_eq_true,ite_false]
    refine ⟨⟨by linarith only [hshort],by linarith only [hh]⟩,?_⟩
    rw [hqeq,sub_eq_add_neg,Circle.exp_add]
    simp only [mul_assoc]

theorem actual_original_corner_external_parameter
    {S : Type*} [TopologicalSpace S] [DecidableEq S]
    (c : Curve S) (b q : Circle) (a z h : ℝ)
    (p : S) (hq : c.map q = p)
    (hp : p = c.map (b*Circle.exp a) ∨ p = c.map (b*Circle.exp z)) :
    let side := decide (p = c.map (b*Circle.exp a))
    let θ := if side then a-h else z+h
    c.map (b*Circle.exp θ) = c.map (q*Circle.exp (if !side then h else -h)) := by
  classical
  by_cases hpa : p = c.map (b*Circle.exp a)
  · have hqeq : q = b*Circle.exp a := c.embedded.injective (hq.trans hpa)
    simp only [hpa,decide_true,ite_true,Bool.not_true,Bool.false_eq_true,ite_false]
    rw [hqeq,sub_eq_add_neg,Circle.exp_add]
    simp only [mul_assoc]
  · have hpz : p = c.map (b*Circle.exp z) := hp.resolve_left hpa
    have hqeq : q = b*Circle.exp z := c.embedded.injective (hq.trans hpz)
    simp only [hpa,decide_false,Bool.false_eq_true,ite_false,Bool.not_false,ite_true]
    rw [hqeq,Circle.exp_add]
    simp only [mul_assoc]

end CurveComplex
