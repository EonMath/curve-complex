import AllBranchCharts

set_option maxHeartbeats 1600000

namespace AlternatingSphereCover

theorem unbranched_cover : IsCoveringMapOn projection (branchFinset : Set Sphere)ᶜ := by
  classical
  have hh : Continuous (fun p : Sphere × Bool × Bool => height p.1) :=
    height_continuous.comp continuous_fst
  have hcraw : IsClosed {p : Sphere × Bool × Bool |
      if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} := by
    have he : {p : Sphere × Bool × Bool |
        if p.2.1 then 0 ≤ height p.1 else height p.1 ≤ 0} =
        {p | p.2.1 = false ∧ height p.1 ≤ 0} ∪
        {p | p.2.1 = true ∧ 0 ≤ height p.1} := by
      ext p
      cases h : p.2.1 <;> simp [h]
    rw [he]
    exact ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le hh continuous_const)).union
      ((isClosed_eq (continuous_fst.comp continuous_snd) continuous_const).inter
      (isClosed_le continuous_const hh))
  letI : CompactSpace Raw := isCompact_iff_compactSpace.mp hcraw.isCompact
  have local_cover (U : Set Sphere) (hU : IsOpen U) (tag : Raw → Bool)
      (ht : Continuous tag) (hf : ∀x, tag (rawDeck x)= !(tag x))
      (hr : ∀x y : Raw, x.val.1∈U → y.val.1∈U →
        (Rel x y ↔ x.val.1=y.val.1 ∧ tag x=tag y)) : IsCoveringMapOn projection U := by
    let RU := {x : Raw // x.val.1∈U}
    let su : Setoid RU := Setoid.comap Subtype.val setoid
    let Q := Quotient su
    let A : Set Total := projection ⁻¹' U
    let pQ : Q → Total := Quotient.map Subtype.val (by intro x y h; exact h)
    have hpQ (q : Q) : pQ q ∈ A := by
      induction q using Quotient.inductionOn with
      | h q => exact q.property
    let qT : Q → A := fun q => ⟨pQ q,hpQ q⟩
    have hqT : Continuous qT := by
      apply Continuous.subtype_mk
      exact (continuous_quotient_mk'.comp continuous_subtype_val).quotient_lift _
    have hqTi : Function.Injective qT := by
      intro x y h
      have he := congrArg Subtype.val h
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y =>
          apply Quotient.sound
          exact (Quotient.exact he : setoid x.val y.val)
    have hqTq : Topology.IsQuotientMap qT := by
      apply Topology.IsQuotientMap.of_comp (f := Quotient.mk su) continuous_quotient_mk' hqT
      exact isQuotientMap_quotient_mk'.restrictPreimage_isOpen (hU.preimage projection_continuous)
    let eT : Q ≃ₜ A :=
      (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hqTq,hqTi⟩).homeomorph qT
    let F : Raw → Sphere × Bool := fun x => (x.val.1,tag x)
    have hF : Continuous F := (continuous_fst.comp continuous_subtype_val).prodMk ht
    have hFs : Function.Surjective F := by
      rintro ⟨b,s⟩
      obtain ⟨x,hxb⟩ : ∃x : Raw, x.val.1=b := by
        by_cases hb : 0≤height b
        · exact ⟨⟨(b,true,false),hb⟩,rfl⟩
        · exact ⟨⟨(b,false,false),le_of_not_ge hb⟩,rfl⟩
      by_cases htag : tag x=s
      · exact ⟨x,Prod.ext hxb htag⟩
      · refine ⟨rawDeck x,Prod.ext hxb ?_⟩
        change tag (rawDeck x)=s
        rw [hf]
        cases hx : tag x <;> cases s <;> simp_all only [Bool.not_false, Bool.not_true, Bool.false_eq_true, Bool.true_eq_false, not_false_eq_true, not_true_eq_false]
    let V : Set (Sphere × Bool) := {p | p.1∈U}
    let eV : V ≃ₜ (U × Bool) := {
      toFun := fun p => (⟨p.val.1,p.property⟩,p.val.2)
      invFun := fun p => ⟨(p.1.val,p.2),p.1.property⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
    let fU : RU → U × Bool := fun x => (⟨x.val.val.1,x.property⟩,tag x.val)
    have hfU : Continuous fU := by
      apply Continuous.prodMk
      · apply Continuous.subtype_mk
        exact continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)
      · exact ht.comp continuous_subtype_val
    let fQ : Q → U × Bool := Quotient.lift fU (by
      intro x y h
      obtain ⟨hb,ht⟩ := (hr x.val y.val x.property y.property).mp h
      exact Prod.ext (Subtype.ext hb) ht)
    have hfQ : Continuous fQ := hfU.quotient_lift _
    have hfUq : Topology.IsQuotientMap fU :=
      eV.isQuotientMap.comp ((hF.isClosedMap.isQuotientMap hF hFs).restrictPreimage_isOpen
        (hU.preimage continuous_fst))
    have hfQq : Topology.IsQuotientMap fQ :=
      Topology.IsQuotientMap.of_comp (f := Quotient.mk su) continuous_quotient_mk' hfQ hfUq
    have hfQi : Function.Injective fQ := by
      intro x y h
      induction x using Quotient.inductionOn with
      | h x =>
        induction y using Quotient.inductionOn with
        | h y =>
          apply Quotient.sound
          apply (hr x.val y.val x.property y.property).mpr
          exact ⟨congrArg (fun p : U × Bool => p.1.val) h,congrArg Prod.snd h⟩
    let eF : Q ≃ₜ U × Bool :=
      (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hfQq,hfQi⟩).homeomorph fQ
    have heq (q : Q) : (eF q).1.val=projection (eT q).val := by
      induction q using Quotient.inductionOn with
      | h q => rfl
    intro b hb
    apply IsEvenlyCovered.to_isEvenlyCovered_preimage (I := Bool)
    refine ⟨inferInstance,U,hb,hU,hU.preimage projection_continuous,eT.symm.trans eF,?_⟩
    intro x
    exact (heq (eT.symm x)).trans (congrArg (fun y : A => projection y.val) (eT.apply_symm_apply x))
  have hemisphere_cover (a : Bool) :
      IsCoveringMapOn projection {b | if a then 0<height b else height b<0} := by
    let U : Set Sphere := {b | if a then 0<height b else height b<0}
    have hU : IsOpen U := by
      cases a
      · exact isOpen_lt height_continuous continuous_const
      · exact isOpen_lt continuous_const height_continuous
    have hhalf (x : Raw) (hx : x.val.1∈U) : x.val.2.1=a := by
      have hp : if x.val.2.1 then 0≤height x.val.1 else height x.val.1≤0 := x.property
      cases a <;> cases he : x.val.2.1
      · rfl
      · change height x.val.1<0 at hx
        simp only [he,↓reduceIte] at hp
        linarith
      · change 0<height x.val.1 at hx
        simp only [he,Bool.false_eq_true,↓reduceIte] at hp
        linarith
      · rfl
    have hnb (x : Raw) (hx : x.val.1∈U) : ¬branch x.val.1 := by
      intro hb
      change (if a then 0<height x.val.1 else height x.val.1<0) at hx
      cases a <;> simp [hb.1] at hx
    apply local_cover U hU (fun x => x.val.2.2)
      (continuous_snd.comp (continuous_snd.comp continuous_subtype_val)) (fun x => rfl)
    intro x y hx hy
    constructor
    · intro h
      refine ⟨h.1,?_⟩
      rcases h.2 with hb | hl
      · exact (hnb x hx hb).elim
      · have he : (x.val.2.2 ^^ (a && decide (0<seamPolynomial x.val.1))) =
            (y.val.2.2 ^^ (a && decide (0<seamPolynomial x.val.1))) := by
          simpa only [label,hhalf x hx,hhalf y hy,h.1] using hl
        exact Bool.xor_left_inj.mp he
    · rintro ⟨hb,hs⟩
      refine ⟨hb,Or.inr ?_⟩
      simp only [label,hhalf x hx,hhalf y hy,hb,hs]
  have seam_cover (a : Bool) :
      IsCoveringMapOn projection {b | if a then 0<seamPolynomial b else seamPolynomial b<0} := by
    let U : Set Sphere := {b | if a then 0<seamPolynomial b else seamPolynomial b<0}
    let tag : Raw → Bool := fun x => x.val.2.2 ^^ (x.val.2.1 && a)
    have hU : IsOpen U := by
      cases a
      · exact isOpen_lt seamPolynomial_continuous continuous_const
      · exact isOpen_lt continuous_const seamPolynomial_continuous
    have htag : Continuous tag :=
      (continuous_of_discreteTopology : Continuous (fun p : Bool × Bool => p.2 ^^ (p.1 && a))).comp
        (continuous_snd.comp continuous_subtype_val)
    have hflip (x : Raw) : tag (rawDeck x)= !(tag x) := by
      exact Bool.not_xor _ _
    have hlabel (x : Raw) (hx : x.val.1∈U) : label x=tag x := by
      have hd : decide (0<seamPolynomial x.val.1)=a := by
        cases a
        · change seamPolynomial x.val.1<0 at hx
          simp [not_lt_of_ge (le_of_lt hx)]
        · change 0<seamPolynomial x.val.1 at hx
          simp [hx]
      simp only [label,tag,hd]
    have hnb (x : Raw) (hx : x.val.1∈U) : ¬branch x.val.1 := by
      intro hb
      change (if a then 0<seamPolynomial x.val.1 else seamPolynomial x.val.1<0) at hx
      cases a <;> simp [hb.2] at hx
    apply local_cover U hU tag htag hflip
    intro x y hx hy
    constructor
    · intro h
      refine ⟨h.1,?_⟩
      rcases h.2 with hb | hl
      · exact (hnb x hx hb).elim
      · exact (hlabel x hx).symm.trans (hl.trans (hlabel y hy))
    · rintro ⟨hb,ht⟩
      exact ⟨hb,Or.inr ((hlabel x hx).trans (ht.trans (hlabel y hy).symm))⟩
  intro b hb
  have hnb : ¬branch b := by simpa only [Set.mem_compl_iff,Finset.mem_coe,mem_branchFinset] using hb
  by_cases hh0 : height b=0
  · have hp0 : seamPolynomial b≠0 := fun h => hnb ⟨hh0,h⟩
    rcases lt_or_gt_of_ne hp0 with h|h
    · exact seam_cover false b h
    · exact seam_cover true b h
  · rcases lt_or_gt_of_ne hh0 with h|h
    · exact hemisphere_cover false b h
    · exact hemisphere_cover true b h
end AlternatingSphereCover
