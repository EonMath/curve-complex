import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualOppositeRectanglesFullStrip
namespace CurveComplex
open Set Schoenflies
set_option maxHeartbeats 6000000

private theorem actual_positive_half_clock_bounds (τ : Interval) (v : ℝ)
    (hv : v ≤ 1) : 0 ≤ (τ : ℝ) * max v 0 ∧ (τ : ℝ) * max v 0 ≤ 1 := by
  have hm0 : 0 ≤ max v 0 := le_max_right v 0
  have hm1 : max v 0 ≤ 1 := max_le hv (by norm_num)
  constructor <;> nlinarith [τ.property.1, τ.property.2]

/-- Construct an ACTUAL two-port middle strip from its four actual transverse
half-arcs. All four boundary joins, both fillings, the full piecewise port
clocks, original literal center, and whole chart localization are derived. -/
theorem actual_four_positive_half_ports_produce_middle_strip
    (P Q M N : C(Interval,Plane))
    (hP : Topology.IsEmbedding P) (hQ : Topology.IsEmbedding Q)
    (hM : Topology.IsEmbedding M) (hN : Topology.IsEmbedding N)
    (a b δ l u : ℝ) (hab : a<b) (hδ : 0<δ)
    (hP0 : P 0=Plane.mk a 0) (hQ0 : Q 0=Plane.mk b 0)
    (hM0 : M 0=Plane.mk a 0) (hN0 : N 0=Plane.mk b 0)
    (hPpos : ∀ t : Interval,0<(t:ℝ) → 0<P t 1)
    (hQpos : ∀ t : Interval,0<(t:ℝ) → 0<Q t 1)
    (hMpos : ∀ t : Interval,0<(t:ℝ) → 0<M t 1)
    (hNpos : ∀ t : Interval,0<(t:ℝ) → 0<N t 1)
    (hδP : δ<P 1 1) (hδQ : δ<Q 1 1) (hδM : δ<M 1 1) (hδN : δ<N 1 1)
    (hsepPQ : ∀ s t,P s 0<Q t 0) (hsepMN : ∀ s t,M s 0<N t 0)
    (hPloc : ∀ t,l≤P t 0 ∧ P t 0≤u) (hQloc : ∀ t,l≤Q t 0 ∧ Q t 0≤u)
    (hMloc : ∀ t,l≤M t 0 ∧ M t 0≤u) (hNloc : ∀ t,l≤N t 0 ∧ N t 0≤u) :
    ∃ τp σp τm σm : Interval,
      0<(τp:ℝ) ∧ 0<(σp:ℝ) ∧ 0<(τm:ℝ) ∧ 0<(σm:ℝ) ∧
    ∃ F : Interval × Icc (-1 : ℝ) 1 → Plane, Topology.IsEmbedding F ∧
      (∀ t,F (t,⟨0,by norm_num⟩)=Plane.mk (a+(b-a)*(t:ℝ)) 0) ∧
      (∀ w : Icc (-1 : ℝ) 1,F (0,w)=if (w:ℝ)≤0 then
        Plane.mk (M ⟨(τm:ℝ)*max (-(w:ℝ)) 0,actual_positive_half_clock_bounds τm (-(w:ℝ)) (by linarith [w.property.1])⟩ 0)
          (-(M ⟨(τm:ℝ)*max (-(w:ℝ)) 0,actual_positive_half_clock_bounds τm (-(w:ℝ)) (by linarith [w.property.1])⟩ 1)) else
        P ⟨(τp:ℝ)*max (w:ℝ) 0,actual_positive_half_clock_bounds τp (w:ℝ) w.property.2⟩) ∧
      (∀ w : Icc (-1 : ℝ) 1,F (1,w)=if (w:ℝ)≤0 then
        Plane.mk (N ⟨(σm:ℝ)*max (-(w:ℝ)) 0,actual_positive_half_clock_bounds σm (-(w:ℝ)) (by linarith [w.property.1])⟩ 0)
          (-(N ⟨(σm:ℝ)*max (-(w:ℝ)) 0,actual_positive_half_clock_bounds σm (-(w:ℝ)) (by linarith [w.property.1])⟩ 1)) else
        Q ⟨(σp:ℝ)*max (w:ℝ) 0,actual_positive_half_clock_bounds σp (w:ℝ) w.property.2⟩) ∧
      (∀ z,l≤F z 0 ∧ F z 0≤u ∧ -δ≤F z 1 ∧ F z 1≤δ) ∧
      (∀ z,F z 1=0 ↔ (z.2:ℝ)=0) := by
  obtain ⟨τp,σp,hτp,hσp,U,hU,hUcenter,hUleft,hUright,hUtop,hUloc,hUzero⟩ :=
    actual_positive_ports_produce_localized_upper_rectangle P Q hP hQ a b δ l u hab hδ
      hP0 hQ0 hPpos hQpos hδP hδQ hsepPQ hPloc hQloc
  obtain ⟨τm,σm,hτm,hσm,V,hV,hVcenter,hVleft,hVright,hVtop,hVloc,hVzero⟩ :=
    actual_positive_ports_produce_localized_upper_rectangle M N hM hN a b δ l u hab hδ
      hM0 hN0 hMpos hNpos hδM hδN hsepMN hMloc hNloc
  let ref : Plane → Plane := fun p => Plane.mk (p 0) (-(p 1))
  have hrc : Continuous ref := by dsimp [ref]; fun_prop
  have hri : Function.Injective ref := by
    intro p q he
    have hh0 := congrArg (fun p : Plane => p 0) he
    have hh1 := congrArg (fun p : Plane => p 1) he
    ext i; fin_cases i
    · exact hh0
    · change p 1 = q 1
      exact neg_injective hh1
  let D := ref ∘ V
  have hD : Topology.IsEmbedding D := ((hrc.comp hV.continuous).isClosedEmbedding
    (hri.comp hV.injective)).isEmbedding
  let C : Interval → Plane := fun t => Plane.mk (a+(b-a)*(t:ℝ)) 0
  have hDcenter : ∀ t,D (t,0)=C t := by
    intro t
    change ref (V (t,0))=C t
    rw [hVcenter]
    ext i; fin_cases i <;> simp [ref,C,Plane.mk]
  have hDy : ∀ z,D z 1≤0 := by
    intro z
    change -(V z 1)≤0
    linarith [(hVloc z).2.2.1]
  have hDz : ∀ z,D z 1=0 ↔ z.2=0 := by
    intro z
    change -(V z 1)=0 ↔ z.2=0
    rw [neg_eq_zero,hVzero]
  obtain ⟨F,hF,hFc,hFval,hFrange,hFzero⟩ :=
    actual_opposite_rectangles_literal_center_full_strip U D hU hD C hUcenter hDcenter
      (fun z => (hUloc z).2.2.1) hDy hUzero hDz
  have hclipplus (w : Icc (-1 : ℝ) 1) (hw : 0≤(w:ℝ)) :
      (projIcc 0 1 zero_le_one (w:ℝ):ℝ)=max (w:ℝ) 0 := by
    rw [max_eq_left hw]
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨hw,w.property.2⟩)
  have hclipminus (w : Icc (-1 : ℝ) 1) (hw : (w:ℝ)≤0) :
      (projIcc 0 1 zero_le_one (-(w:ℝ)):ℝ)=max (-(w:ℝ)) 0 := by
    rw [max_eq_left (by linarith)]
    exact congrArg Subtype.val (projIcc_of_mem zero_le_one ⟨by linarith,by linarith [w.property.1]⟩)
  refine ⟨τp,σp,τm,σm,hτp,hσp,hτm,hσm,F,hF,hFc,?_,?_,?_,hFzero⟩
  · intro w
    rw [hFval]
    by_cases hw : (w:ℝ)≤0
    · rw [ite_eq_left hw,ite_eq_left hw]
      change ref (V (0,projIcc 0 1 zero_le_one (-(w:ℝ))))=ref _
      rw [hVleft]
      apply congrArg ref
      apply congrArg M
      apply Subtype.ext
      change (τm:ℝ)*(projIcc 0 1 zero_le_one (-(w:ℝ)):ℝ)=(τm:ℝ)*max (-(w:ℝ)) 0
      rw [hclipminus w hw]
    · rw [ite_eq_right hw,ite_eq_right hw,hUleft]
      apply congrArg P
      apply Subtype.ext
      change (τp:ℝ)*(projIcc 0 1 zero_le_one (w:ℝ):ℝ)=(τp:ℝ)*max (w:ℝ) 0
      rw [hclipplus w (le_of_not_ge hw)]
  · intro w
    rw [hFval]
    by_cases hw : (w:ℝ)≤0
    · rw [ite_eq_left hw,ite_eq_left hw]
      change ref (V (1,projIcc 0 1 zero_le_one (-(w:ℝ))))=ref _
      rw [hVright]
      apply congrArg ref
      apply congrArg N
      apply Subtype.ext
      change (σm:ℝ)*(projIcc 0 1 zero_le_one (-(w:ℝ)):ℝ)=(σm:ℝ)*max (-(w:ℝ)) 0
      rw [hclipminus w hw]
    · rw [ite_eq_right hw,ite_eq_right hw,hUright]
      apply congrArg Q
      apply Subtype.ext
      change (σp:ℝ)*(projIcc 0 1 zero_le_one (w:ℝ):ℝ)=(σp:ℝ)*max (w:ℝ) 0
      rw [hclipplus w (le_of_not_ge hw)]
  · intro z
    have hz : F z∈Set.range U ∪ Set.range D := hFrange ▸ Set.mem_range_self z
    rcases hz with ⟨v,hv⟩|⟨v,hv⟩
    · rw [← hv]
      have hh := hUloc v
      exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.1],hh.2.2.2⟩
    · rw [← hv]
      have hh := hVloc v
      change l≤V v 0 ∧ V v 0≤u ∧ -δ≤-(V v 1) ∧ -(V v 1)≤δ
      exact ⟨hh.1,hh.2.1,by linarith [hh.2.2.2],by linarith [hh.2.2.1]⟩
end CurveComplex
