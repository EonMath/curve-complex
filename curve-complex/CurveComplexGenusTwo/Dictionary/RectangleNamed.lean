import CurveComplexGenusTwo.Dictionary.ArcPreimageClosed
open Set Topology
namespace CurveComplex
theorem rectangle_cut_package_vertical (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
    ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
      Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
      Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
      Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) ∧
      (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
      (∀ s t, (P.trans Q) s = (P.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
  have hpaths (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d) :
      ∃ P : Path (k,c) (k,d), ∃ Q : Path (k,d) (k,c), ∃ χ : Path (k,c) (k,d),
        Function.Injective P ∧ Function.Injective Q ∧ Function.Injective χ ∧
        Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
          (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
        Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
          (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} ∧
        Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d} ∧
        (∀ s t, (P.trans χ.symm) s = (P.trans χ.symm) t →
          s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
        (∀ s t, (χ.trans Q) s = (χ.trans Q) t →
          s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) ∧
        (∀ s t, (P.trans Q) s = (P.trans Q) t →
          s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0)) := by
    have hH (a b y : ℝ) (hab : a < b) :
      Function.Injective (Path.segment (a, y) (b, y)) ∧
        Set.range (Path.segment (a, y) (b, y)) = {z : ℝ × ℝ | a ≤ z.1 ∧ z.1 ≤ b ∧ z.2 = y} := by
      have hcoord (t : Interval) : Path.segment (a, y) (b, y) t =
          ((1 - (t : ℝ)) * a + (t : ℝ) * b, y) := by
        simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
        ring
      constructor
      · intro s t h
        have hh := congrArg Prod.fst h
        rw [hcoord, hcoord] at hh
        apply Subtype.ext
        dsimp at hh
        nlinarith
      · ext z
        constructor
        · rintro ⟨t, rfl⟩
          rw [hcoord]
          exact ⟨by nlinarith [t.property.1], by nlinarith [t.property.2], rfl⟩
        · rintro ⟨ha, hb, hy⟩
          let t : Interval := ⟨(z.1 - a) / (b - a), by
            constructor
            · exact div_nonneg (sub_nonneg.mpr ha) (sub_pos.mpr hab).le
            · exact (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩
          refine ⟨t, ?_⟩
          rw [hcoord]
          apply Prod.ext
          · dsimp [t]
            field_simp [ne_of_gt (sub_pos.mpr hab)]
            ring
          · exact hy.symm
    have hV (x c d : ℝ) (hcd : c < d) :
      Function.Injective (Path.segment (x, c) (x, d)) ∧
        Set.range (Path.segment (x, c) (x, d)) = {z : ℝ × ℝ | z.1 = x ∧ c ≤ z.2 ∧ z.2 ≤ d} := by
      have hcoord (t : Interval) : Path.segment (x, c) (x, d) t =
          (x, (1 - (t : ℝ)) * c + (t : ℝ) * d) := by
        simp [Path.segment_apply, AffineMap.lineMap_apply, smul_eq_mul]
        ring
      constructor
      · intro s t h
        have hh := congrArg Prod.snd h
        rw [hcoord, hcoord] at hh
        apply Subtype.ext
        dsimp at hh
        nlinarith
      · ext z
        constructor
        · rintro ⟨t, rfl⟩
          rw [hcoord]
          exact ⟨rfl, by nlinarith [t.property.1], by nlinarith [t.property.2]⟩
        · rintro ⟨hx, hc, hd⟩
          let t : Interval := ⟨(z.2 - c) / (d - c), by
            constructor
            · exact div_nonneg (sub_nonneg.mpr hc) (sub_pos.mpr hcd).le
            · exact (div_le_one (sub_pos.mpr hcd)).mpr (by linarith)⟩
          refine ⟨t, ?_⟩
          rw [hcoord]
          apply Prod.ext
          · exact hx.symm
          · dsimp [t]
            field_simp [ne_of_gt (sub_pos.mpr hcd)]
            ring
    have hcat {X : Type} [TopologicalSpace X] (a b c : X) (P : Path a b) (Q : Path b c)
      (hP : Function.Injective P) (hQ : Function.Injective Q)
      (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = b) :
      Function.Injective (P.trans Q) := by
      have hmeet : ∀ s t, P s = Q t → s = 1 ∧ t = 0 := by
        intro s t h
        have hb := hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩
        exact ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
      intro s t h
      simp only [Path.trans_apply] at h
      split_ifs at h with hs ht ht
      · have hh := congrArg Subtype.val (hP h)
        apply Subtype.ext
        dsimp at hh
        linarith
      · obtain ⟨h1, h0⟩ := hmeet _ _ h
        apply Subtype.ext
        have h1 := congrArg Subtype.val h1
        have h0 := congrArg Subtype.val h0
        dsimp at h1 h0
        linarith
      · obtain ⟨h1, h0⟩ := hmeet _ _ h.symm
        apply Subtype.ext
        have h1 := congrArg Subtype.val h1
        have h0 := congrArg Subtype.val h0
        dsimp at h1 h0
        linarith
      · have hh := congrArg Subtype.val (hQ h)
        apply Subtype.ext
        dsimp at hh
        linarith
    have hloop {X : Type} [TopologicalSpace X] (a b : X) (P : Path a b) (Q : Path b a)
      (hP : Function.Injective P) (hQ : Function.Injective Q)
      (hset : ∀ z ∈ Set.range P, z ∈ Set.range Q → z = a ∨ z = b) :
      ∀ s t, (P.trans Q) s = (P.trans Q) t →
        s = t ∨ (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
      have hmeet : ∀ s t, P s = Q t → (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 0) := by
        intro s t h
        rcases hset (P s) ⟨s, rfl⟩ ⟨t, h.symm⟩ with ha | hb
        · exact Or.inl ⟨hP (ha.trans P.source.symm), hQ (h.symm.trans (ha.trans Q.target.symm))⟩
        · exact Or.inr ⟨hP (hb.trans P.target.symm), hQ (h.symm.trans (hb.trans Q.source.symm))⟩
      intro s t h
      simp only [Path.trans_apply] at h
      split_ifs at h with hs ht ht
      · left
        have hh := congrArg Subtype.val (hP h)
        apply Subtype.ext
        dsimp at hh
        linarith
      · rcases hmeet _ _ h with ⟨hs0, ht1⟩ | ⟨hs1, ht0⟩
        · right; left
          constructor
          · apply Subtype.ext
            have := congrArg Subtype.val hs0
            dsimp at this
            change (s : ℝ) = 0
            linarith
          · apply Subtype.ext
            have := congrArg Subtype.val ht1
            dsimp at this
            change (t : ℝ) = 1
            linarith
        · left
          apply Subtype.ext
          have h1 := congrArg Subtype.val hs1
          have h0 := congrArg Subtype.val ht0
          dsimp at h1 h0
          linarith
      · rcases hmeet _ _ h.symm with ⟨ht0, hs1⟩ | ⟨ht1, hs0⟩
        · right; right
          constructor
          · apply Subtype.ext
            have := congrArg Subtype.val hs1
            dsimp at this
            change (s : ℝ) = 1
            linarith
          · apply Subtype.ext
            have := congrArg Subtype.val ht0
            dsimp at this
            change (t : ℝ) = 0
            linarith
        · left
          apply Subtype.ext
          have h1 := congrArg Subtype.val ht1
          have h0 := congrArg Subtype.val hs0
          dsimp at h1 h0
          linarith
      · left
        have hh := congrArg Subtype.val (hQ h)
        apply Subtype.ext
        dsimp at hh
        linarith
    let B := (Path.segment (a,c) (k,c)).symm
    let L := Path.segment (a,c) (a,d)
    let T := Path.segment (a,d) (k,d)
    let P := (B.trans L).trans T
    let U := Path.segment (k,d) (b,d)
    let R := (Path.segment (b,c) (b,d)).symm
    let V := (Path.segment (k,c) (b,c)).symm
    let Q := (U.trans R).trans V
    let χ := Path.segment (k,c) (k,d)
    obtain ⟨hBi, hBr⟩ := hH a k c hak
    obtain ⟨hLi, hLr⟩ := hV a c d hcd
    obtain ⟨hTi, hTr⟩ := hH a k d hak
    obtain ⟨hUi, hUr⟩ := hH k b d hkb
    obtain ⟨hRi, hRr⟩ := hV b c d hcd
    obtain ⟨hVi, hVr⟩ := hH k b c hkb
    obtain ⟨hχi, hχr⟩ := hV k c d hcd
    have hBsr : Set.range B = Set.range (Path.segment (a,c) (k,c)) := Path.symm_range _
    have hRsr : Set.range R = Set.range (Path.segment (b,c) (b,d)) := Path.symm_range _
    have hVsr : Set.range V = Set.range (Path.segment (k,c) (b,c)) := Path.symm_range _
    have hBsi : Function.Injective B := hBi.comp (by
      intro s t h
      apply Subtype.ext
      have h := congrArg Subtype.val h
      dsimp at h
      linarith)
    have hRsi : Function.Injective R := hRi.comp (by
      intro s t h
      apply Subtype.ext
      have h := congrArg Subtype.val h
      dsimp at h
      linarith)
    have hVsi : Function.Injective V := hVi.comp (by
      intro s t h
      apply Subtype.ext
      have h := congrArg Subtype.val h
      dsimp at h
      linarith)
    have hBLi : Function.Injective (B.trans L) := hcat _ _ _ B L hBsi hLi (by
      intro z hz hz'
      rw [hBsr, hBr] at hz
      rw [hLr] at hz'
      exact Prod.ext hz'.1 hz.2.2)
    have hPi : Function.Injective P := hcat _ _ _ (B.trans L) T hBLi hTi (by
      intro z hz hz'
      rw [Path.trans_range, hBsr, hBr, hLr] at hz
      rw [hTr] at hz'
      rcases hz with hz | hz
      · exact False.elim ((ne_of_lt hcd) (hz.2.2.symm.trans hz'.2.2))
      · exact Prod.ext hz.1 hz'.2.2)
    have hURi : Function.Injective (U.trans R) := hcat _ _ _ U R hUi hRsi (by
      intro z hz hz'
      rw [hUr] at hz
      rw [hRsr, hRr] at hz'
      exact Prod.ext hz'.1 hz.2.2)
    have hQi : Function.Injective Q := hcat _ _ _ (U.trans R) V hURi hVsi (by
      intro z hz hz'
      rw [Path.trans_range, hUr, hRsr, hRr] at hz
      rw [hVsr, hVr] at hz'
      rcases hz with hz | hz
      · exact False.elim ((ne_of_lt hcd) (hz'.2.2.symm.trans hz.2.2))
      · exact Prod.ext hz.1 hz'.2.2)
    have hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
        (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
      change Set.range ((B.trans L).trans T) = _
      rw [Path.trans_range, Path.trans_range, hBsr, hBr, hLr, hTr]
      ext z
      simp only [mem_union, mem_ofPred_eq]
      tauto
    have hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
        (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
      change Set.range ((U.trans R).trans V) = _
      rw [Path.trans_range, Path.trans_range, hUr, hRsr, hRr, hVsr, hVr]
      ext z
      simp only [mem_union, mem_ofPred_eq]
      tauto
    have hχsi : Function.Injective χ.symm := hχi.comp (by
      intro s t h
      apply Subtype.ext
      have h := congrArg Subtype.val h
      dsimp at h
      linarith)
    refine ⟨P, Q, χ, hPi, hQi, hχi, hPr, hQr, hχr, ?_, ?_, ?_⟩
    · apply hloop _ _ P χ.symm hPi hχsi
      intro z hz hz'
      rw [hPr] at hz
      rw [Path.symm_range, hχr] at hz'
      rcases hz with hz | hz
      · rcases hz.2.2 with hy | hy
        · exact Or.inl (Prod.ext hz'.1 hy)
        · exact Or.inr (Prod.ext hz'.1 hy)
      · exact False.elim ((ne_of_lt hak) (hz.1.symm.trans hz'.1))
    · apply hloop _ _ χ Q hχi hQi
      intro z hz hz'
      rw [hχr] at hz
      rw [hQr] at hz'
      rcases hz' with hz' | hz'
      · rcases hz'.2.2 with hy | hy
        · exact Or.inl (Prod.ext hz.1 hy)
        · exact Or.inr (Prod.ext hz.1 hy)
      · exact False.elim ((ne_of_lt hkb) (hz.1.symm.trans hz'.1))
    · apply hloop _ _ P Q hPi hQi
      intro z hz hz'
      rw [hPr] at hz
      rw [hQr] at hz'
      rcases hz with hz | hz <;> rcases hz' with hz' | hz'
      · have hx : z.1 = k := le_antisymm hz.2.1 hz'.1
        rcases hz.2.2 with hy | hy
        · exact Or.inl (Prod.ext hx hy)
        · exact Or.inr (Prod.ext hx hy)
      · exact False.elim (not_le_of_gt hkb (hz'.1 ▸ hz.2.1))
      · exact False.elim (not_le_of_gt hak (hz.1 ▸ hz'.1))
      · exact False.elim (ne_of_lt (lt_trans hak hkb) (hz.1.symm.trans hz'.1))
  
  have hranges (a k b c d : ℝ) (hak : a < k) (hkb : k < b) (hcd : c < d)
      (P : Path (k,c) (k,d)) (Q : Path (k,d) (k,c)) (χ : Path (k,c) (k,d))
      (hPr : Set.range P = {z : ℝ × ℝ | (a ≤ z.1 ∧ z.1 ≤ k ∧ (z.2 = c ∨ z.2 = d)) ∨
        (z.1 = a ∧ c ≤ z.2 ∧ z.2 ≤ d)})
      (hQr : Set.range Q = {z : ℝ × ℝ | (k ≤ z.1 ∧ z.1 ≤ b ∧ (z.2 = c ∨ z.2 = d)) ∨
        (z.1 = b ∧ c ≤ z.2 ∧ z.2 ≤ d)})
      (hχr : Set.range χ = {z : ℝ × ℝ | z.1 = k ∧ c ≤ z.2 ∧ z.2 ≤ d}) :
      Set.range (P.trans χ.symm) = frontier (Icc a k ×ˢ Icc c d) ∧
      Set.range (χ.trans Q) = frontier (Icc k b ×ˢ Icc c d) ∧
      Set.range (P.trans Q) = frontier (Icc a b ×ˢ Icc c d) := by
    have hfront (u v : ℝ) (huv : u < v) :
        frontier (Icc u v ×ˢ Icc c d) =
        {z : ℝ × ℝ | (u ≤ z.1 ∧ z.1 ≤ v ∧ (z.2 = c ∨ z.2 = d)) ∨
          ((z.1 = u ∨ z.1 = v) ∧ c ≤ z.2 ∧ z.2 ≤ d)} := by
      rw [frontier_prod_eq, isClosed_Icc.closure_eq, isClosed_Icc.closure_eq,
        frontier_Icc huv.le, frontier_Icc hcd.le]
      ext z
      simp only [mem_union, mem_prod, mem_Icc, mem_insert_iff, mem_singleton_iff, mem_ofPred_eq]
      tauto
    constructor
    · rw [Path.trans_range, Path.symm_range, hPr, hχr, hfront a k hak]
      ext z
      simp only [mem_union, mem_ofPred_eq]
      tauto
    constructor
    · rw [Path.trans_range, hχr, hQr, hfront k b hkb]
      ext z
      simp only [mem_union, mem_ofPred_eq]
      tauto
    · rw [Path.trans_range, hPr, hQr, hfront a b (lt_trans hak hkb)]
      ext z
      simp only [mem_union, mem_ofPred_eq]
      constructor
      · rintro ((⟨hx, hk, hy⟩ | ⟨hx, hc, hd⟩) | (⟨hk, hb, hy⟩ | ⟨hx, hc, hd⟩))
        · exact Or.inl ⟨hx, le_trans hk hkb.le, hy⟩
        · exact Or.inr ⟨Or.inl hx, hc, hd⟩
        · exact Or.inl ⟨le_trans hak.le hk, hb, hy⟩
        · exact Or.inr ⟨Or.inr hx, hc, hd⟩
      · rintro (⟨ha, hb, hy⟩ | ⟨hx, hc, hd⟩)
        · rcases le_total z.1 k with hk | hk
          · exact Or.inl (Or.inl ⟨ha, hk, hy⟩)
          · exact Or.inr (Or.inl ⟨hk, hb, hy⟩)
        · rcases hx with hx | hx
          · exact Or.inl (Or.inr ⟨hx, hc, hd⟩)
          · exact Or.inr (Or.inr ⟨hx, hc, hd⟩)
  
  obtain ⟨P,Q,χ,_,_,_,hp,hq,hχ,hleft,hright,houter⟩ := hpaths a k b c d hak hkb hcd
  obtain ⟨hl,hr,ho⟩ := hranges a k b c d hak hkb hcd P Q χ hp hq hχ
  exact ⟨P,Q,χ,hl,hr,ho,hleft,hright,houter⟩
end CurveComplex
