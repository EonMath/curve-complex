import CurveComplexGenusTwo.Topology.ActualHarerDiskGluing.CompactKernelTransport

open CurveComplex Set Topology
namespace ActualHarerDiskGluing

/-- The only permitted fiber collapses are the flagged literal endpoints. -/
def collapsedEndpoint (c₀ c₁ : Bool) (t : Interval) : Prop :=
  (c₀ = true ∧ t = 0) ∨ (c₁ = true ∧ t = 1)

def squareBoundary : Set (Interval × Interval) :=
  {z | z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1}

/-- Explicit finite model for the disk and the optionally collapsed collar. -/
theorem optional_collapse_model (c₀ c₁ : Bool) (hnotBoth : ¬ (c₀=true ∧ c₁=true)) :
    ∃ A B : C(Interval × Interval,Interval × Interval),
      Function.Injective A ∧
      (∀ t u t' u', B (t,u)=B (t',u') ↔
        t=t' ∧ (u=u' ∨ collapsedEndpoint c₀ c₁ t)) ∧
      (∀ t u t' u', A (t,u)=B (t',u') ↔
        t=t' ∧ u=1 ∧ (u'=0 ∨ collapsedEndpoint c₀ c₁ t)) ∧
      Function.Surjective (Sum.elim A B) ∧
      (∀ t u, A (t,u) ∈ squareBoundary ↔ t=0 ∨ t=1 ∨ u=0) ∧
      (∀ t u, B (t,u) ∈ squareBoundary ↔ t=0 ∨ t=1 ∨ u=1) := by
  classical
  let h : C(Interval,ℝ) := ⟨fun t => if c₀ then (t:ℝ) else if c₁ then 1-(t:ℝ) else 1,by
    cases c₀ <;> cases c₁ <;> simp <;> fun_prop⟩
  have hn (t : Interval) : 0 ≤ h t := by
    cases c₀ <;> cases c₁ <;> simp [h] <;> linarith [t.property.1,t.property.2]
  have hz (t : Interval) : h t=0 ↔ collapsedEndpoint c₀ c₁ t := by
    cases c₀ <;> cases c₁
    · simp [h,collapsedEndpoint]
    · simp only [h,ContinuousMap.coe_mk,Bool.false_eq_true,↓reduceIte,
        Bool.true_eq_false,not_false_eq_true,collapsedEndpoint,false_and,true_and,false_or]
      exact ⟨fun hh => Subtype.ext (by change (t:ℝ)=1; linarith),fun hh => by rw [hh]; norm_num⟩
    · simp only [h,ContinuousMap.coe_mk,↓reduceIte,collapsedEndpoint,
        Bool.false_eq_true,false_and,or_false,true_and]
      exact ⟨fun hh => Subtype.ext hh,fun hh => congrArg Subtype.val hh⟩
    · exact False.elim (hnotBoth ⟨rfl,rfl⟩)
  have hend (t : Interval) (hh : h t=0) : t=0 ∨ t=1 := by
    rcases (hz t).mp hh with ⟨_,ht⟩ | ⟨_,ht⟩
    · exact Or.inl ht
    · exact Or.inr ht
  have hp (t : Interval) : 0 < 1+h t := by linarith [hn t]
  have hne (t : Interval) : 1+h t ≠ 0 := (hp t).ne'
  have hcDen : Continuous (fun z : Interval × Interval => 1+h z.1) :=
    continuous_const.add (h.continuous.comp continuous_fst)
  have hcA : Continuous (fun z : Interval × Interval => (z.2:ℝ)/(1+h z.1)) :=
    (continuous_subtype_val.comp continuous_snd).div hcDen (fun z => hne z.1)
  have hcB : Continuous (fun z : Interval × Interval => (1+h z.1*(z.2:ℝ))/(1+h z.1)) :=
    (continuous_const.add ((h.continuous.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))).div hcDen (fun z => hne z.1)
  let A : C(Interval × Interval,Interval × Interval) :=
    ⟨fun z => (z.1,⟨(z.2:ℝ)/(1+h z.1),⟨div_nonneg z.2.property.1 (hp z.1).le,
      (div_le_one (hp z.1)).mpr (by linarith [z.2.property.2,hn z.1])⟩⟩),continuous_fst.prodMk (hcA.subtype_mk _)⟩
  let B : C(Interval × Interval,Interval × Interval) :=
    ⟨fun z => (z.1,⟨(1+h z.1*(z.2:ℝ))/(1+h z.1),⟨
      div_nonneg (by nlinarith [hn z.1,z.2.property.1]) (hp z.1).le,
      (div_le_one (hp z.1)).mpr (by nlinarith [hn z.1,z.2.property.2])⟩⟩),continuous_fst.prodMk (hcB.subtype_mk _)⟩
  have hAi : Function.Injective A := by
    rintro ⟨t,u⟩ ⟨t',u'⟩ he
    have ht : t=t' := congrArg Prod.fst he
    subst t'
    refine Prod.ext (by rfl) ?_
    apply Subtype.ext
    have hu := congrArg (fun z : Interval × Interval => (z.2:ℝ)) he
    change (u:ℝ)/(1+h t)=(u':ℝ)/(1+h t) at hu
    exact (div_left_inj' (hne t)).mp hu
  have hBk (t u t' u' : Interval) : B (t,u)=B (t',u') ↔
      t=t' ∧ (u=u' ∨ collapsedEndpoint c₀ c₁ t) := by
    constructor
    · intro he
      have ht : t=t' := congrArg Prod.fst he
      subst t'
      refine ⟨rfl,?_⟩
      have hu := congrArg (fun z : Interval × Interval => (z.2:ℝ)) he
      change (1+h t*(u:ℝ))/(1+h t)=(1+h t*(u':ℝ))/(1+h t) at hu
      have he' := (div_left_inj' (hne t)).mp hu
      by_cases hh : h t=0
      · exact Or.inr ((hz t).mp hh)
      · left
        apply Subtype.ext
        exact (mul_left_cancel₀ hh (by linarith : h t*(u:ℝ)=h t*(u':ℝ)))
    · rintro ⟨rfl,hu | hh⟩
      · rw [hu]
      · refine Prod.ext (by rfl) ?_
        apply Subtype.ext
        change (1+h t*(u:ℝ))/(1+h t)=(1+h t*(u':ℝ))/(1+h t)
        rw [(hz t).mpr hh]
        simp
  have hAB (t u t' u' : Interval) : A (t,u)=B (t',u') ↔
      t=t' ∧ u=1 ∧ (u'=0 ∨ collapsedEndpoint c₀ c₁ t) := by
    constructor
    · intro he
      have ht : t=t' := congrArg Prod.fst he
      subst t'
      have hu := congrArg (fun z : Interval × Interval => (z.2:ℝ)) he
      change (u:ℝ)/(1+h t)=(1+h t*(u':ℝ))/(1+h t) at hu
      have he' := (div_left_inj' (hne t)).mp hu
      have hu1 : u=1 := Subtype.ext (by change (u:ℝ)=1; nlinarith [hn t,u'.property.1,u.property.2])
      refine ⟨rfl,hu1,?_⟩
      have hmul : h t*(u':ℝ)=0 := by rw [hu1] at he'; change 1=1+h t*(u':ℝ) at he'; linarith
      rcases mul_eq_zero.mp hmul with hh | hh
      · exact Or.inr ((hz t).mp hh)
      · exact Or.inl (Subtype.ext hh)
    · rintro ⟨rfl,rfl,hu | hh⟩
      · refine Prod.ext (by rfl) ?_
        apply Subtype.ext
        change 1/(1+h t)=(1+h t*(u':ℝ))/(1+h t)
        rw [hu]; simp
      · refine Prod.ext (by rfl) ?_
        apply Subtype.ext
        change 1/(1+h t)=(1+h t*(u':ℝ))/(1+h t)
        rw [(hz t).mpr hh]; simp
  have hs : Function.Surjective (Sum.elim A B) := by
    rintro ⟨t,v⟩
    by_cases hv : (1+h t)*(v:ℝ) ≤ 1
    · let u : Interval := ⟨(1+h t)*(v:ℝ),⟨mul_nonneg (hp t).le v.property.1,hv⟩⟩
      refine ⟨Sum.inl (t,u),Prod.ext rfl (Subtype.ext ?_)⟩
      change ((1+h t)*(v:ℝ))/(1+h t)=(v:ℝ)
      field_simp [hne t]
    · have hh : 0 < h t := by nlinarith [hn t,v.property.2]
      let u : Interval := ⟨((1+h t)*(v:ℝ)-1)/h t,⟨
        div_nonneg (by linarith) hh.le,
        (div_le_one hh).mpr (by nlinarith [v.property.2])⟩⟩
      refine ⟨Sum.inr (t,u),Prod.ext rfl (Subtype.ext ?_)⟩
      change (1+h t*(((1+h t)*(v:ℝ)-1)/h t))/(1+h t)=(v:ℝ)
      field_simp [hne t,hh.ne']
      <;> ring
  have hAbd (t u : Interval) : A (t,u) ∈ squareBoundary ↔ t=0 ∨ t=1 ∨ u=0 := by
    change t=0 ∨ t=1 ∨ (⟨(u:ℝ)/(1+h t),_⟩ : Interval)=0 ∨
      (⟨(u:ℝ)/(1+h t),_⟩ : Interval)=1 ↔ _
    constructor
    · rintro (ht | ht | hu | hu)
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · right; right
        apply Subtype.ext
        have he := congrArg Subtype.val hu
        change (u:ℝ)/(1+h t)=0 at he
        exact (div_eq_zero_iff).mp he |>.resolve_right (hne t)
      · have he := congrArg Subtype.val hu
        change (u:ℝ)/(1+h t)=1 at he
        have he' := (div_eq_one_iff_eq (hne t)).mp he
        have hz' : h t=0 := by linarith [u.property.2,hn t]
        rcases hend t hz' with ht | ht
        · exact Or.inl ht
        · exact Or.inr (Or.inl ht)
    · rintro (ht | ht | hu)
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · right; right; left; apply Subtype.ext
        change (u:ℝ)/(1+h t)=0
        rw [hu]; simp
  have hBbd (t u : Interval) : B (t,u) ∈ squareBoundary ↔ t=0 ∨ t=1 ∨ u=1 := by
    change t=0 ∨ t=1 ∨ (⟨(1+h t*(u:ℝ))/(1+h t),_⟩ : Interval)=0 ∨
      (⟨(1+h t*(u:ℝ))/(1+h t),_⟩ : Interval)=1 ↔ _
    constructor
    · rintro (ht | ht | hu | hu)
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · have he := congrArg Subtype.val hu
        change (1+h t*(u:ℝ))/(1+h t)=0 at he
        have he' := (div_eq_zero_iff).mp he |>.resolve_right (hne t)
        nlinarith [hn t,u.property.1]
      · have he := congrArg Subtype.val hu
        change (1+h t*(u:ℝ))/(1+h t)=1 at he
        have he' := (div_eq_one_iff_eq (hne t)).mp he
        by_cases hh : h t=0
        · rcases hend t hh with ht | ht
          · exact Or.inl ht
          · exact Or.inr (Or.inl ht)
        · right; right
          apply Subtype.ext
          exact mul_left_cancel₀ hh (by linarith : h t*(u:ℝ)=h t*1)
    · rintro (ht | ht | hu)
      · exact Or.inl ht
      · exact Or.inr (Or.inl ht)
      · right; right; right; apply Subtype.ext
        change (1+h t*(u:ℝ))/(1+h t)=1
        rw [hu]; simp [hne t]
  exact ⟨A,B,hAi,hBk,hAB,hs,hAbd,hBbd⟩

end ActualHarerDiskGluing
