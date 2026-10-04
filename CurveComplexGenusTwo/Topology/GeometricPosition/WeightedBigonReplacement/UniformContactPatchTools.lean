import CurveComplexGenusTwo.Topology.GeometricPosition.SquareSupportSurface
import Mathlib.Topology.Order.IntermediateValue
open Set Topology Metric Schoenflies
namespace CurveComplex

-- Uniform small-height contact patches and actual endpoint clearance.
theorem actual_uniform_radial_contact_patch {J : Type*} [Fintype J]
    (a b : J → Plane) (ha : ∀ j, 0 < a j 1) (hb : ∀ j, b j 1 < 0)
    (η : ℝ) (hη : 0 < η) :
    ∃ δ H : ℝ, 0 < δ ∧ 0 < H ∧
      Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η ∧
      Plane.mk δ 0 ∈ Metric.ball (0 : Plane) η ∧ ∀ h : ℝ, 0 < h → h < H →
      let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
      C ⊆ Metric.ball (0 : Plane) η ∧
      (∀ j, Plane.mk (-δ) h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ∧
      (∀ j, Plane.mk δ h ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j)) ∧
      Disjoint C {x | x 1 = 0} ∧
      (∀ j, (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).Finite ∧
        (C ∩ (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))).ncard ≤ 1) := by
  classical
  have hCounts (a b : Plane) (ha : 0 < a 1) (hb : b 1 < 0) (δ h : ℝ) (hh : 0 < h) :
      let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
      Disjoint C {x | x 1 = 0} ∧
      (C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b)).Finite ∧
      (C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b)).ncard ≤ 1 := by
    let C := segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h)
    have hCy (x : Plane) (hx : x ∈ C) : x 1 = h := by
      change x ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) at hx
      rw [segment_eq_image'] at hx
      obtain ⟨t,ht,he⟩ := hx
      have hy := congrArg (fun z : Plane => z 1) he
      change h+t*(h-h) = x 1 at hy
      simpa using hy.symm
    have hLower : Disjoint C (segment ℝ (0 : Plane) b) := by
      apply Set.disjoint_left.mpr
      intro x hx hxB
      rw [segment_eq_image'] at hxB
      obtain ⟨t,ht,he⟩ := hxB
      have hy := congrArg (fun z : Plane => z 1) he
      change 0+t*(b 1-0) = x 1 at hy
      rw [hCy x hx] at hy
      nlinarith [ht.1]
    have hSingle : (C ∩ segment ℝ (0 : Plane) a).Subsingleton := by
      intro x hx y hy
      rw [segment_eq_image'] at hx hy
      obtain ⟨t,ht,he⟩ := hx.2
      obtain ⟨s,hs,hse⟩ := hy.2
      have hxt := congrArg (fun z : Plane => z 1) he
      have hys := congrArg (fun z : Plane => z 1) hse
      change 0+t*(a 1-0) = x 1 at hxt
      change 0+s*(a 1-0) = y 1 at hys
      rw [hCy x hx.1] at hxt
      rw [hCy y hy.1] at hys
      have hts : t = s := by nlinarith
      exact he.symm.trans (hts ▸ hse)
    have hset : C ∩ (segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b) = C ∩ segment ℝ (0 : Plane) a := by
      rw [Set.inter_union_distrib_left,Set.disjoint_iff_inter_eq_empty.mp hLower,Set.union_empty]
    refine ⟨Set.disjoint_left.mpr (fun x hx hx0 => ?_),?_,?_⟩
    · have hy := hCy x hx
      change x 1 = 0 at hx0
      linarith
    · rw [hset]
      exact hSingle.finite
    · rw [hset]
      exact (Set.ncard_le_one hSingle.finite).mpr hSingle
  have hZero : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
  have hOpen : IsOpen {t : ℝ | Plane.mk (-t) 0 ∈ ball (0 : Plane) η ∧ Plane.mk t 0 ∈ ball (0 : Plane) η} := by
    exact (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (by fun_prop))
  have h0 : (0 : ℝ) ∈ {t : ℝ | Plane.mk (-t) 0 ∈ ball (0 : Plane) η ∧ Plane.mk t 0 ∈ ball (0 : Plane) η} := by
    constructor <;> simpa [neg_zero,hZero] using hη
  obtain ⟨r,hr,hBall⟩ := Metric.isOpen_iff.mp hOpen 0 h0
  let δ := r/2
  have hδ : 0 < δ := half_pos hr
  have hBase := hBall (show δ ∈ ball (0 : ℝ) r by
    rw [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hδ]; dsimp [δ]; linarith only [hr])
  let O : Set Plane := Metric.ball (0 : Plane) η ∩
    ⋂ j, (segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j))ᶜ
  have hO : IsOpen O := Metric.isOpen_ball.inter (isOpen_iInter_of_finite (fun j =>
    ((isCompact_segment (0 : Plane) (a j)).isClosed.union
      (isCompact_segment (0 : Plane) (b j)).isClosed).isOpen_compl))
  have hAxisAvoid (ξ : ℝ) (hξ : ξ ≠ 0) :
      ∀ j, Plane.mk ξ 0 ∉ segment ℝ (0 : Plane) (a j) ∪ segment ℝ (0 : Plane) (b j) := by
    intro j hj
    have hOne (v : Plane) (hv : v 1 ≠ 0) (hm : Plane.mk ξ 0 ∈ segment ℝ (0 : Plane) v) : False := by
      rw [segment_eq_image'] at hm
      obtain ⟨t,ht,he⟩ := hm
      have hy := congrArg (fun z : Plane => z 1) he
      change 0+t*(v 1-0) = 0 at hy
      have ht0 : t = 0 := (mul_eq_zero.mp (by simpa using hy)).resolve_right hv
      rw [ht0] at he
      have hx := congrArg (fun z : Plane => z 0) he
      change 0+0*(v 0-0) = ξ at hx
      exact hξ (by simpa using hx.symm)
    exact hj.elim (hOne (a j) (ne_of_gt (ha j))) (hOne (b j) (ne_of_lt (hb j)))
  have hBoth : Plane.mk (-δ) 0 ∈ O ∧ Plane.mk δ 0 ∈ O :=
    ⟨⟨hBase.1,Set.mem_iInter.mpr (hAxisAvoid (-δ) (neg_ne_zero.mpr (ne_of_gt hδ)))⟩,
      ⟨hBase.2,Set.mem_iInter.mpr (hAxisAvoid δ (ne_of_gt hδ))⟩⟩
  have hopenH : IsOpen {h : ℝ | Plane.mk (-δ) h ∈ O ∧ Plane.mk δ h ∈ O} :=
    (hO.preimage (by fun_prop)).inter (hO.preimage (by fun_prop))
  obtain ⟨H,hH,hEnds⟩ := Metric.isOpen_iff.mp hopenH 0 hBoth
  refine ⟨δ,H,hδ,hH,hBase.1,hBase.2,?_⟩
  intro h hh hhH
  have he := hEnds (show h ∈ Metric.ball (0 : ℝ) H by
    simpa [Real.dist_eq,abs_of_pos hh] using hhH)
  refine ⟨(convex_ball (0 : Plane) η).segment_subset he.1.1 he.2.1,
    Set.mem_iInter.mp he.1.2,Set.mem_iInter.mp he.2.2,?_,?_⟩
  · apply Set.disjoint_left.mpr
    intro z hz hz0
    rw [segment_eq_image'] at hz
    obtain ⟨t,ht,he⟩ := hz
    have hy := congrArg (fun q : Plane => q 1) he
    change h+t*(h-h) = z 1 at hy
    change z 1 = 0 at hz0
    simp only [sub_self,mul_zero,add_zero] at hy
    exact (ne_of_gt hh) (hy.trans hz0)
  · intro j
    exact (hCounts (a j) (b j) (ha j) (hb j) δ h hh).2
-- Actual chart transition along the original side gives endpoint order;
-- a wiggling chart off the side does not affect this one-dimensional fact.
theorem actual_contact_axis_transition_order
    {S : Type*} [TopologicalSpace S]
    (F E : OpenPartialHomeomorph S Plane) (p : S) (δ : ℝ) (hδ : 0 < δ)
    (hp : p ∈ F.source) (hFp : F p = 0)
    (hTarget : ∀ x ∈ Set.Icc (-δ) δ, Plane.mk x 0 ∈ F.target)
    (hSource : F.source ⊆ E.source)
    (hAxis : ∀ x ∈ Set.Icc (-δ) δ, E (F.symm (Plane.mk x 0)) 1 = 0) :
    let f := fun x : ℝ => E (F.symm (Plane.mk x 0)) 0
    (f (-δ) < E p 0 ∧ E p 0 < f δ) ∨
      (f δ < E p 0 ∧ E p 0 < f (-δ)) := by
  let f := fun x : ℝ => E (F.symm (Plane.mk x 0)) 0
  have hpath : ContinuousOn (fun x : ℝ => F.symm (Plane.mk x 0)) (Set.Icc (-δ) δ) :=
    F.symm.continuousOn.comp (by fun_prop) hTarget
  have hEpath : ContinuousOn (fun x : ℝ => E (F.symm (Plane.mk x 0))) (Set.Icc (-δ) δ) :=
    E.continuousOn.comp hpath (fun x hx => hSource (F.map_target (hTarget x hx)))
  have hf : ContinuousOn f (Set.Icc (-δ) δ) :=
    (show Continuous (fun z : Plane => z 0) from by fun_prop).continuousOn.comp hEpath
      (fun _ _ => Set.mem_univ _)
  have hi : Set.InjOn f (Set.Icc (-δ) δ) := by
    intro x hx y hy he
    have hEeq : E (F.symm (Plane.mk x 0)) = E (F.symm (Plane.mk y 0)) := by
      ext i
      fin_cases i
      · exact he
      · exact (hAxis x hx).trans (hAxis y hy).symm
    have hFeq := E.injOn (hSource (F.map_target (hTarget x hx)))
      (hSource (F.map_target (hTarget y hy))) hEeq
    have hpeq := F.symm.injOn (hTarget x hx) (hTarget y hy) hFeq
    exact congrArg (fun z : Plane => z 0) hpeq
  have hf0 : f 0 = E p 0 := by
    have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
    dsimp [f]
    rw [hz,← hFp,F.left_inv hp]
  have hzero : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith only [hδ],hδ.le⟩
  have hl : (-δ : ℝ) ∈ Set.Icc (-δ) δ := ⟨le_rfl,by linarith only [hδ]⟩
  have hr : δ ∈ Set.Icc (-δ) δ := ⟨by linarith only [hδ],le_rfl⟩
  rcases hf.strictMonoOn_of_injOn_Icc' (by linarith only [hδ]) hi with hm | ha
  · left
    rw [← hf0]
    exact ⟨hm hl hzero (neg_neg_of_pos hδ),hm hzero hr hδ⟩
  · right
    rw [← hf0]
    exact ⟨ha hzero hr hδ,ha hl hzero (neg_neg_of_pos hδ)⟩

theorem actual_axis_interval_in_ball (δ η : ℝ) (hδ : 0 < δ)
    (hl : Plane.mk (-δ) 0 ∈ Metric.ball (0 : Plane) η)
    (hr : Plane.mk δ 0 ∈ Metric.ball (0 : Plane) η) :
    ∀ x ∈ Set.Icc (-δ) δ, Plane.mk x 0 ∈ Metric.ball (0 : Plane) η := by
  intro x hx
  apply (convex_ball (0 : Plane) η).segment_subset hl hr
  rw [segment_eq_image']
  refine ⟨(x+δ)/(2*δ),⟨?_,?_⟩,?_⟩
  · exact div_nonneg (by linarith only [hx.1]) (by positivity)
  · apply (div_le_one (by positivity : 0 < 2*δ)).mpr
    linarith only [hx.2]
  · ext i
    fin_cases i
    · change -δ+(x+δ)/(2*δ)*(δ- -δ) = x
      have hd : 2*δ ≠ 0 := by positivity
      field_simp
      ring
    · simp

theorem actual_connected_axis_coordinate_bounds
    (A : Set ℝ) (hA : IsPreconnected A) (a b x : ℝ)
    (hx : x ∈ A) (hax : a < x) (hxb : x < b) (ha : a ∉ A) (hb : b ∉ A) :
    A ⊆ Set.Ioo a b := by
  intro y hy
  constructor
  · by_contra hn
    exact ha (hA.Icc_subset hy hx ⟨le_of_not_gt hn,hax.le⟩)
  · by_contra hn
    exact hb (hA.Icc_subset hx hy ⟨hxb.le,le_of_not_gt hn⟩)

theorem actual_radial_star_axis_membership (a b : Plane) (ha : a 1 ≠ 0) (hb : b 1 ≠ 0)
    (x : ℝ) :
    Plane.mk x 0 ∈ segment ℝ (0 : Plane) a ∪ segment ℝ (0 : Plane) b ↔ x = 0 := by
  constructor
  · intro hx
    have hOne (v : Plane) (hv : v 1 ≠ 0) (hm : Plane.mk x 0 ∈ segment ℝ (0 : Plane) v) : x = 0 := by
      rw [segment_eq_image'] at hm
      obtain ⟨t,ht,he⟩ := hm
      have hy := congrArg (fun z : Plane => z 1) he
      change 0+t*(v 1-0) = 0 at hy
      have ht0 : t = 0 := (mul_eq_zero.mp (by simpa using hy)).resolve_right hv
      rw [ht0] at he
      have hx := congrArg (fun z : Plane => z 0) he
      change 0+0*(v 0-0) = x at hx
      simpa using hx.symm
    exact hx.elim (hOne a ha) (hOne b hb)
  · rintro rfl
    left
    have hz : Plane.mk (0 : ℝ) 0 = (0 : Plane) := by ext i; fin_cases i <;> rfl
    rw [hz]
    exact left_mem_segment ℝ _ _

theorem actual_continuous_injective_axis_image
    (f : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc (-δ) δ)) (hi : Set.InjOn f (Set.Icc (-δ) δ)) :
    ∃ L R : ℝ, L < f 0 ∧ f 0 < R ∧
      f '' Set.Icc (-δ) δ = Set.Icc L R ∧
      ((L = f (-δ) ∧ R = f δ) ∨ (L = f δ ∧ R = f (-δ))) := by
  have hl : (-δ : ℝ) ∈ Set.Icc (-δ) δ := ⟨le_rfl,by linarith only [hδ]⟩
  have hr : δ ∈ Set.Icc (-δ) δ := ⟨by linarith only [hδ],le_rfl⟩
  have hz : (0 : ℝ) ∈ Set.Icc (-δ) δ := ⟨by linarith only [hδ],hδ.le⟩
  rcases hc.strictMonoOn_of_injOn_Icc' (by linarith only [hδ]) hi with hm | ha
  · exact ⟨f (-δ),f δ,hm hl hz (neg_neg_of_pos hδ),hm hz hr hδ,
      hc.image_Icc_of_monotoneOn (by linarith only [hδ]) hm.monotoneOn,Or.inl ⟨rfl,rfl⟩⟩
  · exact ⟨f δ,f (-δ),ha hz hr hδ,ha hl hz (neg_neg_of_pos hδ),
      hc.image_Icc_of_antitoneOn (by linarith only [hδ]) ha.antitoneOn,Or.inr ⟨rfl,rfl⟩⟩

theorem actual_horizontal_contact_endpoint_families
    {S : Type*} [TopologicalSpace S]
    (F : OpenPartialHomeomorph S Plane) (δ H : ℝ) (hH : 0 < H)
    (hleft : Plane.mk (-δ) 0 ∈ F.target) (hright : Plane.mk δ 0 ∈ F.target)
    (hTarget : ∀ h : ℝ, 0 < h → h < H →
      segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) ⊆ F.target) :
    ∃ L R : C(Interval,S), L 0 = F.symm (Plane.mk (-δ) 0) ∧
      R 0 = F.symm (Plane.mk δ 0) ∧
      (∀ t, L t ∈ F.source ∧ L t = F.symm (Plane.mk (-δ) ((H/2)*t.val))) ∧
      (∀ t, R t ∈ F.source ∧ R t = F.symm (Plane.mk δ ((H/2)*t.val))) := by
  have hparam (t : Interval) (ht : t.val ≠ 0) :
      0 < (H/2)*t.val ∧ (H/2)*t.val < H := by
    have hp : 0 < t.val := lt_of_le_of_ne t.property.1 (Ne.symm ht)
    exact ⟨mul_pos (half_pos hH) hp,by nlinarith [t.property.2]⟩
  let l : Interval → Plane := fun t => Plane.mk (-δ) ((H/2)*t.val)
  let r : Interval → Plane := fun t => Plane.mk δ ((H/2)*t.val)
  have hl : Continuous l := by fun_prop
  have hr : Continuous r := by fun_prop
  have hlt (t : Interval) : l t ∈ F.target := by
    by_cases ht : t.val = 0
    · simpa [l,ht] using hleft
    · exact hTarget _ (hparam t ht).1 (hparam t ht).2 (left_mem_segment ℝ _ _)
  have hrt (t : Interval) : r t ∈ F.target := by
    by_cases ht : t.val = 0
    · simpa [r,ht] using hright
    · exact hTarget _ (hparam t ht).1 (hparam t ht).2 (right_mem_segment ℝ _ _)
  let L : C(Interval,S) := ⟨fun t => F.symm (l t),F.symm.continuousOn.comp_continuous hl hlt⟩
  let R : C(Interval,S) := ⟨fun t => F.symm (r t),F.symm.continuousOn.comp_continuous hr hrt⟩
  refine ⟨L,R,?_,?_,?_,?_⟩
  · change F.symm (l 0) = F.symm (Plane.mk (-δ) 0)
    simp [l]
  · change F.symm (r 0) = F.symm (Plane.mk δ 0)
    simp [r]
  · intro t
    exact ⟨F.map_target (hlt t),rfl⟩
  · intro t
    exact ⟨F.map_target (hrt t),rfl⟩

theorem actual_reverse_embedded_continuous_arc
    {S : Type*} [TopologicalSpace S] (f : C(Interval,S)) (hf : Topology.IsEmbedding f) :
    ∃ g : C(Interval,S), Topology.IsEmbedding g ∧ Set.range g = Set.range f ∧ g 0 = f 1 ∧ g 1 = f 0 := by
  let g : C(Interval,S) := f.comp ⟨unitInterval.symmHomeomorph,unitInterval.symmHomeomorph.continuous⟩
  refine ⟨g,hf.comp unitInterval.symmHomeomorph.isEmbedding,?_,?_,?_⟩
  · change Set.range (f ∘ unitInterval.symmHomeomorph) = Set.range f
    exact unitInterval.symmHomeomorph.surjective.range_comp f
  · change f (unitInterval.symmHomeomorph 0) = f 1
    simp
  · change f (unitInterval.symmHomeomorph 1) = f 0
    simp

theorem actual_contact_axis_choose_inner_width
    (f : ℝ → ℝ) (δ L R : ℝ) (hδ : 0 < δ)
    (hc : ContinuousOn f (Set.Icc (-δ) δ)) (hL : L < f 0) (hR : f 0 < R) :
    ∃ d : ℝ, 0 < d ∧ d < δ ∧ ∀ x ∈ Set.Icc (-d) d, L < f x ∧ f x < R := by
  have hf : ContinuousAt f 0 := hc.continuousAt (Icc_mem_nhds (neg_neg_of_pos hδ) hδ)
  have hpre : f ⁻¹' Set.Ioo L R ∈ nhds (0 : ℝ) :=
    hf.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨hL,hR⟩)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hpre
  let d := min r δ/2
  have hd : 0 < d := half_pos (lt_min hr hδ)
  have hdr : d < r := by dsimp [d]; have := min_le_left r δ; linarith only [hr,this]
  have hdδ : d < δ := by dsimp [d]; have := min_le_right r δ; linarith only [hδ,this]
  refine ⟨d,hd,hdδ,?_⟩
  intro x hx
  exact hball (show x ∈ Metric.ball (0 : ℝ) r by
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_lt]
    constructor <;> linarith only [hx.1,hx.2,hdr])

theorem actual_horizontal_contact_subsegment (δ d h : ℝ)
    (hδ : 0 < δ) (hd : 0 < d) (hsmall : d < δ) :
    segment ℝ (Plane.mk (-d) h) (Plane.mk d h) ⊆
      segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) := by
  have hpoint (x : ℝ) (hx : x ∈ Set.Icc (-δ) δ) :
      Plane.mk x h ∈ segment ℝ (Plane.mk (-δ) h) (Plane.mk δ h) := by
    rw [segment_eq_image']
    refine ⟨(x+δ)/(2*δ),⟨?_,?_⟩,?_⟩
    · exact div_nonneg (by linarith only [hx.1]) (by positivity)
    · apply (div_le_one (by positivity : 0 < 2*δ)).mpr
      linarith only [hx.2]
    · ext i
      fin_cases i
      · change -δ+(x+δ)/(2*δ)*(δ- -δ) = x
        field_simp
        ring
      · simp
  exact (convex_segment (Plane.mk (-δ) h) (Plane.mk δ h)).segment_subset
    (hpoint (-d) ⟨by linarith only [hsmall],by linarith only [hd,hδ]⟩)
    (hpoint d ⟨by linarith only [hd,hδ],hsmall.le⟩)

end CurveComplex
