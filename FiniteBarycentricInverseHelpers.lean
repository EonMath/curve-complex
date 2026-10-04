import C0RelativeCarrierScaffold

open CurveComplex Set Topology
open scoped BigOperators
open C0RelativeCarrier

attribute [local instance] instDecidable_c0RelativeCarrierScaffold
  instDecidableEq_c0RelativeCarrierScaffold
set_option autoImplicit false

namespace C0RelativeCarrier.BarycentricInverseHelpers

/-- Consecutive positive coordinate levels reconstruct every nonnegative finite
coordinate function. The predecessor is the maximum of the lower attained
levels together with the zero sentinel; no normalization or nonemptiness of V
is assumed. -/
theorem finite_positive_level_gap_reconstruction
    {V : Type*} [Fintype V] (p : V → ℝ)
    (hp : ∀ v, 0 ≤ p v) :
    let L : Finset ℝ := (Finset.univ.image p).filter (fun a => 0 < a)
    let predecessor : ℝ → ℝ := fun a =>
      (({(0 : ℝ)} : Finset ℝ) ∪ L.filter (fun b => b < a)).max'
        (by simp)
    let delta : ℝ → ℝ := fun a => a - predecessor a
    (∀ a ∈ L, 0 < delta a) ∧
      (∀ v, ∑ a ∈ L, (if a ≤ p v then delta a else 0) = p v) := by
  let L : Finset ℝ := (Finset.univ.image p).filter (fun a => 0 < a)
  let predecessor : ℝ → ℝ := fun a =>
    (({(0 : ℝ)} : Finset ℝ) ∪ L.filter (fun b => b < a)).max' (by simp)
  let delta : ℝ → ℝ := fun a => a - predecessor a
  change (∀ a ∈ L, 0 < delta a) ∧
    (∀ v, ∑ a ∈ L, (if a ≤ p v then delta a else 0) = p v)
  have hpos : ∀ a ∈ L, 0 < a := fun a ha => (Finset.mem_filter.mp ha).2
  have hsum : ∀ s : Finset ℝ, (∀ a ∈ s, 0 < a) →
      (∑ a ∈ s, (a -
        (({(0 : ℝ)} : Finset ℝ) ∪ s.filter (fun b => b < a)).max' (by simp))) =
      (({(0 : ℝ)} : Finset ℝ) ∪ s).max' (by simp) := by
    intro s
    induction s using Finset.induction_on_max with
    | empty =>
        intro hs
        simp
    | insert a s hlt ih =>
        intro hs
        have ha : 0 < a := hs a (by simp)
        have hnot : a ∉ s := fun h => (lt_irrefl a) (hlt a h)
        have hfilter : (insert a s).filter (fun b => b < a) = s := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_insert]
          constructor
          · rintro ⟨rfl | hb, hba⟩
            · exact (lt_irrefl _ hba).elim
            · exact hb
          · intro hb
            exact ⟨Or.inr hb, hlt b hb⟩
        have hfilters : ∀ b ∈ s,
            (insert a s).filter (fun c => c < b) = s.filter (fun c => c < b) := by
          intro b hb
          simp [Finset.filter_insert, not_lt.mpr (hlt b hb).le]
        have hmax : (({(0 : ℝ)} : Finset ℝ) ∪ insert a s).max' (by simp) = a := by
          apply (Finset.max'_eq_iff _ _ a).mpr
          constructor
          · simp
          · intro b hb
            rcases Finset.mem_union.mp hb with hb | hb
            · have hb0 : b = 0 := Finset.mem_singleton.mp hb
              simpa [hb0] using ha.le
            · rcases Finset.mem_insert.mp hb with rfl | hb
              · exact le_rfl
              · exact (hlt b hb).le
        rw [hmax, Finset.sum_insert hnot]
        rw [hfilter]
        have heq :
            (∑ b ∈ s, (b -
              (({(0 : ℝ)} : Finset ℝ) ∪ (insert a s).filter (fun c => c < b)).max'
                (by simp))) =
            ∑ b ∈ s, (b -
              (({(0 : ℝ)} : Finset ℝ) ∪ s.filter (fun c => c < b)).max' (by simp)) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [hfilters b hb]
        rw [heq, ih (fun b hb => hs b (Finset.mem_insert_of_mem hb))]
        ring
  constructor
  · intro a ha
    apply sub_pos.mpr
    apply (Finset.max'_lt_iff _ _).mpr
    intro b hb
    rcases Finset.mem_union.mp hb with hb | hb
    · have hb0 : b = 0 := Finset.mem_singleton.mp hb
      simpa [hb0] using hpos a ha
    · exact (Finset.mem_filter.mp hb).2
  · intro v
    let s : Finset ℝ := L.filter (fun a => a ≤ p v)
    have hfilters : ∀ a ∈ s, s.filter (fun b => b < a) = L.filter (fun b => b < a) := by
      intro a ha
      have hav : a ≤ p v := (Finset.mem_filter.mp ha).2
      ext b
      simp only [s, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hb, hbv⟩, hba⟩
        exact ⟨hb, hba⟩
      · rintro ⟨hb, hba⟩
        exact ⟨⟨hb, hba.le.trans hav⟩, hba⟩
    have hmax : (({(0 : ℝ)} : Finset ℝ) ∪ s).max' (by simp) = p v := by
      apply (Finset.max'_eq_iff _ _ (p v)).mpr
      constructor
      · by_cases hv : 0 < p v
        · apply Finset.mem_union_right
          apply Finset.mem_filter.mpr
          refine ⟨?_, le_rfl⟩
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩, hv⟩
        · have hv0 : p v = 0 := le_antisymm (not_lt.mp hv) (hp v)
          simp [hv0]
      · intro a ha
        rcases Finset.mem_union.mp ha with ha | ha
        · have ha0 : a = 0 := Finset.mem_singleton.mp ha
          simpa [ha0] using hp v
        · exact (Finset.mem_filter.mp ha).2
    calc
      (∑ a ∈ L, if a ≤ p v then delta a else 0) = ∑ a ∈ s, delta a :=
        (Finset.sum_filter _ _).symm
      _ = ∑ a ∈ s, (a -
          (({(0 : ℝ)} : Finset ℝ) ∪ s.filter (fun b => b < a)).max' (by simp)) := by
        apply Finset.sum_congr rfl
        intro a ha
        dsimp only [delta, predecessor]
        rw [hfilters a ha]
      _ = (({(0 : ℝ)} : Finset ℝ) ∪ s).max' (by simp) :=
        hsum s (fun a ha => hpos a (Finset.mem_filter.mp ha).1)
      _ = p v := hmax

/-- The exact finite barycenter coordinate map is injective on arbitrary
nonnegative coefficient functions whose positive faces form inclusion chains.
Coefficients are raw: there is deliberately no sum-to-one hypothesis, and the
positive support may be empty. -/
theorem nonnegative_chain_barycenter_injective
    {V : Type*} [Fintype V] (D : AbstractSimplicialComplex V)
    (c d : Face D → ℝ)
    (hc : ∀ σ, 0 ≤ c σ)
    (hd : ∀ σ, 0 ≤ d σ)
    (hc_chain : ∀ σ τ, 0 < c σ → 0 < c τ →
      σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val)
    (hd_chain : ∀ σ τ, 0 < d σ → 0 < d τ →
      σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val)
    (hbar : ∀ v,
      (∑ σ : Face D, if v ∈ σ.val then c σ / (σ.val.card : ℝ) else 0) =
      ∑ σ : Face D, if v ∈ σ.val then d σ / (σ.val.card : ℝ) else 0) :
    c = d := by
  classical
  let B : (Face D → ℝ) → V → ℝ := fun a v =>
    ∑ σ : Face D, if v ∈ σ.val then a σ else 0
  have hface : ∀ σ : Face D, σ.val.Nonempty := fun σ =>
    (D.isRelLowerSet_faces σ.property).1
  have hmax : ∀ (s : Finset (Face D)), s.Nonempty →
      (∀ σ ∈ s, ∀ τ ∈ s, σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val) →
      ∃ τ ∈ s, ∀ σ ∈ s, σ.val ⊆ τ.val := by
    intro s hs hchain
    obtain ⟨τ, hτ, hτmax⟩ := s.exists_max_image (fun σ => σ.val.card) hs
    refine ⟨τ, hτ, ?_⟩
    intro σ hσ
    rcases hchain σ hσ τ hτ with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h (hτmax σ hσ)).symm.subset
  have htop : ∀ (a : Face D → ℝ),
      (∀ σ, 0 ≤ a σ) →
      (∀ σ τ, 0 < a σ → 0 < a τ → σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val) →
      (∃ σ, 0 < a σ) →
      ∃ τ, 0 < a τ ∧ (∀ σ, 0 < a σ → σ.val ⊆ τ.val) ∧
        (∀ v, 0 < B a v ↔ v ∈ τ.val) ∧
        (∀ v ∈ τ.val, a τ ≤ B a v) ∧
        (∃ v ∈ τ.val, B a v = a τ) := by
    intro a ha hchain hpos
    let s : Finset (Face D) := Finset.univ.filter (fun σ => 0 < a σ)
    have hmem : ∀ σ, σ ∈ s ↔ 0 < a σ := by simp [s]
    have hs : s.Nonempty := by
      obtain ⟨σ, hσ⟩ := hpos
      exact ⟨σ, (hmem σ).mpr hσ⟩
    obtain ⟨τ, hτ, hτmax⟩ := hmax s hs (by
      intro σ hσ υ hυ
      exact hchain σ υ ((hmem σ).mp hσ) ((hmem υ).mp hυ))
    have hτpos : 0 < a τ := (hmem τ).mp hτ
    have hmax' : ∀ σ, 0 < a σ → σ.val ⊆ τ.val := fun σ hσ =>
      hτmax σ ((hmem σ).mpr hσ)
    have hterm : ∀ v σ, 0 ≤ (if v ∈ σ.val then a σ else 0) := by
      intro v σ
      split_ifs
      · exact ha σ
      · exact le_rfl
    have hlower : ∀ v ∈ τ.val, a τ ≤ B a v := by
      intro v hv
      have hh := Finset.single_le_sum (s := Finset.univ)
        (fun σ _ => hterm v σ) (Finset.mem_univ τ)
      simpa only [ite_eq_left hv] using hh
    have hsupport : ∀ v, 0 < B a v ↔ v ∈ τ.val := by
      intro v
      constructor
      · intro hv
        by_contra hn
        have hz : B a v = 0 := by
          apply Finset.sum_eq_zero
          intro σ _
          by_cases hm : v ∈ σ.val
          · have hnpos : ¬0 < a σ := fun hσ => hn (hmax' σ hσ hm)
            have heq : a σ = 0 := le_antisymm (le_of_not_gt hnpos) (ha σ)
            simp [heq]
          · simp [hm]
        rw [hz] at hv
        exact (lt_irrefl 0) hv
      · intro hv
        exact lt_of_lt_of_le hτpos (hlower v hv)
    obtain ⟨v, hv, hvonly⟩ : ∃ v ∈ τ.val,
        ∀ σ ∈ s, σ ≠ τ → v ∉ σ.val := by
      by_cases hs' : (s.erase τ).Nonempty
      · obtain ⟨η, hη, hηmax⟩ := hmax (s.erase τ) hs' (by
          intro σ hσ υ hυ
          exact hchain σ υ ((hmem σ).mp (Finset.mem_of_mem_erase hσ))
            ((hmem υ).mp (Finset.mem_of_mem_erase hυ)))
        have hηsub : η.val ⊆ τ.val := hτmax η (Finset.mem_of_mem_erase hη)
        have hηne : η.val ≠ τ.val := by
          intro heq
          exact (Finset.ne_of_mem_erase hη) (Subtype.ext heq)
        have hlt : η.val.card < τ.val.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hηsub, hηne⟩)
        obtain ⟨v, hv, hnv⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
        refine ⟨v, hv, ?_⟩
        intro σ hσ hστ hvσ
        exact hnv (hηmax σ (Finset.mem_erase.mpr ⟨hστ, hσ⟩) hvσ)
      · obtain ⟨v, hv⟩ := hface τ
        refine ⟨v, hv, ?_⟩
        intro σ hσ hστ
        exact False.elim (hs' ⟨σ, Finset.mem_erase.mpr ⟨hστ, hσ⟩⟩)
    refine ⟨τ, hτpos, hmax', hsupport, hlower, v, hv, ?_⟩
    change (∑ σ : Face D, if v ∈ σ.val then a σ else 0) = a τ
    rw [Finset.sum_eq_single τ]
    · simp [hv]
    · intro σ _ hστ
      by_cases hσ : 0 < a σ
      · simp [hvonly σ ((hmem σ).mpr hσ) hστ]
      · have heq : a σ = 0 := le_antisymm (le_of_not_gt hσ) (ha σ)
        simp [heq]
    · simp
  have hnoPos : ∀ (a : Face D → ℝ), (∀ σ, 0 ≤ a σ) →
      (¬∃ σ, 0 < a σ) → ∀ v, B a v = 0 := by
    intro a ha hn v
    apply Finset.sum_eq_zero
    intro σ _
    have heq : a σ = 0 := le_antisymm
      (le_of_not_gt (fun hσ => hn ⟨σ, hσ⟩)) (ha σ)
    simp [heq]
  have hzero : ∀ (a : Face D → ℝ), (∀ σ, 0 ≤ a σ) →
      (∀ v, B a v = 0) → ∀ σ, a σ = 0 := by
    intro a ha hz σ
    obtain ⟨v, hv⟩ := hface σ
    have hh := Finset.single_le_sum (s := Finset.univ)
      (f := fun υ : Face D => if v ∈ υ.val then a υ else 0)
      (by intro υ _; split_ifs; exact ha υ; exact le_rfl)
      (Finset.mem_univ σ)
    have hle : a σ ≤ B a v := by simpa only [ite_eq_left hv] using hh
    exact le_antisymm (by simpa [hz v] using hle) (ha σ)
  have hpeel : ∀ (a : Face D → ℝ) (τ : Face D) (v : V),
      B a v = B (fun σ => if σ = τ then 0 else a σ) v +
        (if v ∈ τ.val then a τ else 0) := by
    intro a τ v
    calc
      B a v = ∑ σ : Face D,
          ((if v ∈ σ.val then (if σ = τ then 0 else a σ) else 0) +
            if σ = τ then (if v ∈ τ.val then a τ else 0) else 0) := by
        apply Finset.sum_congr rfl
        intro σ _
        by_cases hστ : σ = τ
        · subst σ; simp
        · simp [hστ]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [B]
  have hinj : ∀ (s : Finset (Face D)) (a b : Face D → ℝ),
      (∀ σ, 0 ≤ a σ) → (∀ σ, 0 ≤ b σ) →
      (∀ σ τ, 0 < a σ → 0 < a τ → σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val) →
      (∀ σ τ, 0 < b σ → 0 < b τ → σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val) →
      (∀ σ, 0 < a σ → σ ∈ s) → (∀ v, B a v = B b v) → a = b := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s ih a b ha hb hac hbc hsa hB
    by_cases hap : ∃ σ, 0 < a σ
    · obtain ⟨τ, hτpos, hτmax, hτsupport, hτlower, v, hv, hvatop⟩ :=
        htop a ha hac hap
      have hbp : ∃ σ, 0 < b σ := by
        by_contra hn
        have hz := hnoPos b hb hn v
        have hle := hτlower v hv
        rw [hB v, hz] at hle
        exact (not_lt_of_ge hle) hτpos
      obtain ⟨υ, hυpos, hυmax, hυsupport, hυlower, w, hw, hwtop⟩ :=
        htop b hb hbc hbp
      have ht : τ = υ := by
        apply Subtype.ext
        apply Finset.ext
        intro z
        rw [← hτsupport z, ← hυsupport z, hB z]
      subst υ
      have hcoeff : a τ = b τ := by
        have hvb := hυlower v hv
        have hwa := hτlower w hw
        rw [← hB v, hvatop] at hvb
        rw [hB w, hwtop] at hwa
        exact le_antisymm hwa hvb
      let a' : Face D → ℝ := fun σ => if σ = τ then 0 else a σ
      let b' : Face D → ℝ := fun σ => if σ = τ then 0 else b σ
      have ha' : ∀ σ, 0 ≤ a' σ := by
        intro σ
        dsimp [a']
        split_ifs
        · exact le_rfl
        · exact ha σ
      have hb' : ∀ σ, 0 ≤ b' σ := by
        intro σ
        dsimp [b']
        split_ifs
        · exact le_rfl
        · exact hb σ
      have hac' : ∀ σ υ, 0 < a' σ → 0 < a' υ →
          σ.val ⊆ υ.val ∨ υ.val ⊆ σ.val := by
        intro σ υ hσ hυ
        have hσa : 0 < a σ := by
          by_cases heq : σ = τ
          · simp [a', heq] at hσ
          · simpa [a', heq] using hσ
        have hυa : 0 < a υ := by
          by_cases heq : υ = τ
          · simp [a', heq] at hυ
          · simpa [a', heq] using hυ
        exact hac σ υ hσa hυa
      have hbc' : ∀ σ υ, 0 < b' σ → 0 < b' υ →
          σ.val ⊆ υ.val ∨ υ.val ⊆ σ.val := by
        intro σ υ hσ hυ
        have hσb : 0 < b σ := by
          by_cases heq : σ = τ
          · simp [b', heq] at hσ
          · simpa [b', heq] using hσ
        have hυb : 0 < b υ := by
          by_cases heq : υ = τ
          · simp [b', heq] at hυ
          · simpa [b', heq] using hυ
        exact hbc σ υ hσb hυb
      have hs' : ∀ σ, 0 < a' σ → σ ∈ s.erase τ := by
        intro σ hσ
        have hστ : σ ≠ τ := by
          intro heq
          simp [a', heq] at hσ
        exact Finset.mem_erase.mpr ⟨hστ, hsa σ (by simpa [a', hστ] using hσ)⟩
      have hB' : ∀ z, B a' z = B b' z := by
        intro z
        have haB := hpeel a τ z
        have hbB := hpeel b τ z
        change B a z = B a' z + (if z ∈ τ.val then a τ else 0) at haB
        change B b z = B b' z + (if z ∈ τ.val then b τ else 0) at hbB
        rw [hB z, hcoeff] at haB
        exact add_right_cancel (haB.symm.trans hbB)
      have hab' : a' = b' := ih (s.erase τ) (Finset.erase_ssubset (hsa τ hτpos))
        a' b' ha' hb' hac' hbc' hs' hB'
      funext σ
      by_cases hστ : σ = τ
      · subst σ; exact hcoeff
      · have hh := congrFun hab' σ
        simpa [a', b', hστ] using hh
    · have ha0 := hnoPos a ha hap
      have hb0 : ∀ z, B b z = 0 := fun z => (hB z).symm.trans (ha0 z)
      funext σ
      exact (hzero a ha ha0 σ).trans (hzero b hb hb0 σ).symm
  have hcard : ∀ σ : Face D, (0 : ℝ) < σ.val.card := by
    intro σ
    exact_mod_cast Finset.card_pos.mpr (hface σ)
  let a : Face D → ℝ := fun σ => c σ / (σ.val.card : ℝ)
  let b : Face D → ℝ := fun σ => d σ / (σ.val.card : ℝ)
  have ha : ∀ σ, 0 ≤ a σ := fun σ => div_nonneg (hc σ) (hcard σ).le
  have hb : ∀ σ, 0 ≤ b σ := fun σ => div_nonneg (hd σ) (hcard σ).le
  have hac : ∀ σ τ, 0 < a σ → 0 < a τ →
      σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val := by
    intro σ τ hσ hτ
    exact hc_chain σ τ ((div_pos_iff_of_pos_right (hcard σ)).mp hσ)
      ((div_pos_iff_of_pos_right (hcard τ)).mp hτ)
  have hbc : ∀ σ τ, 0 < b σ → 0 < b τ →
      σ.val ⊆ τ.val ∨ τ.val ⊆ σ.val := by
    intro σ τ hσ hτ
    exact hd_chain σ τ ((div_pos_iff_of_pos_right (hcard σ)).mp hσ)
      ((div_pos_iff_of_pos_right (hcard τ)).mp hτ)
  have hab : a = b := hinj Finset.univ a b ha hb hac hbc
    (by intro σ _; exact Finset.mem_univ σ) hbar
  funext σ
  exact (div_left_inj' (ne_of_gt (hcard σ))).mp (congrFun hab σ)

end C0RelativeCarrier.BarycentricInverseHelpers
