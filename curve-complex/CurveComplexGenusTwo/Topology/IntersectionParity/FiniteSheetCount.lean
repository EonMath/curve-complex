import Mathlib
namespace CurveComplex.LocalSurgery

/-- Sum the actual local sheet flips along a finite ordered event set.
This is only the discrete interval bookkeeping after every geometric local
flip has been proved; it is not a parity hypothesis on surface curves. -/
theorem finite_sheet_flips_endpoint_count
    (events : Finset ℝ) (hinside : ∀ u ∈ events, 0 < u ∧ u < 1)
    (sheet : ℝ → ZMod 2)
    (hcontinuous : ContinuousOn sheet (Set.Icc 0 1 \ (events : Set ℝ)))
    (hflip : ∀ u ∈ events, ∃ δ : ℝ, 0 < δ ∧
      ∀ v w : ℝ, u - δ < v → v < u → u < w → w < u + δ →
        sheet v = sheet w + 1) :
    sheet 0 = sheet 1 + (events.card : ZMod 2) := by
  classical
  have aux : ∀ (s : Finset ℝ) (b : ℝ), 0 ≤ b →
      (∀ u ∈ s, 0 < u ∧ u < b) →
      ContinuousOn sheet (Set.Icc 0 b \ (s : Set ℝ)) →
      (∀ u ∈ s, ∃ δ : ℝ, 0 < δ ∧
        ∀ v w : ℝ, u - δ < v → v < u → u < w → w < u + δ →
          sheet v = sheet w + 1) →
      sheet 0 = sheet b + (s.card : ZMod 2) := by
    intro s
    induction s using Finset.induction_on_max with
    | empty =>
      intro b hb hi hc hf
      have he : sheet 0 = sheet b := (isPreconnected_Icc (a := 0) (b := b)).constant
        (hc.mono (by simp)) (by exact ⟨le_rfl, hb⟩) (by exact ⟨hb, le_rfl⟩)
      simpa using he
    | insert u s hmax ih =>
      intro b hb hi hc hf
      have hu : 0 < u ∧ u < b := hi u (Finset.mem_insert_self _ _)
      have hus : u ∉ s := by intro h; exact (lt_irrefl u) (hmax u h)
      obtain ⟨δ, hδ, hlocal⟩ := hf u (Finset.mem_insert_self _ _)
      obtain ⟨r, hr0, hru, hr⟩ : ∃ r : ℝ, 0 ≤ r ∧ r < u ∧ ∀ x ∈ s, x ≤ r := by
        rcases s.eq_empty_or_nonempty with hs | hs
        · subst s
          exact ⟨0, le_rfl, hu.1, by simp⟩
        · refine ⟨max 0 (s.max' hs), le_max_left _ _, max_lt hu.1 (hmax _ (s.max'_mem hs)), ?_⟩
          intro x hx
          exact (s.le_max' x hx).trans (le_max_right _ _)
      obtain ⟨v, hvlow, hvu⟩ := exists_between (max_lt hru (by linarith : u - δ < u))
      have hv0 : 0 < v := lt_of_le_of_lt hr0 (lt_of_le_of_lt (le_max_left _ _) hvlow)
      have hrv : r < v := lt_of_le_of_lt (le_max_left _ _) hvlow
      have hvδ : u - δ < v := lt_of_le_of_lt (le_max_right _ _) hvlow
      obtain ⟨w, huw, hwup⟩ := exists_between (lt_min hu.2 (by linarith : u < u + δ))
      have hwb : w < b := lt_of_lt_of_le hwup (min_le_left _ _)
      have hwδ : w < u + δ := lt_of_lt_of_le hwup (min_le_right _ _)
      have hleft : sheet 0 = sheet v + (s.card : ZMod 2) := ih v hv0.le
        (by intro x hx; exact ⟨(hi x (Finset.mem_insert_of_mem hx)).1, (hr x hx).trans_lt hrv⟩)
        (hc.mono (by
          intro x hx
          refine ⟨⟨hx.1.1, hx.1.2.trans (hvu.trans hu.2).le⟩, ?_⟩
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
          intro hh
          rcases hh with hh | hh
          · subst x; linarith [hx.1.2]
          · exact hx.2 hh))
        (by intro x hx; exact hf x (Finset.mem_insert_of_mem hx))
      have hright : sheet w = sheet b := (isPreconnected_Icc (a := w) (b := b)).constant
        (hc.mono (by
          intro x hx
          refine ⟨⟨by linarith [hx.1, hu.1], hx.2⟩, ?_⟩
          simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe]
          intro hh
          rcases hh with hh | hh
          · subst x; linarith [hx.1]
          · have := hmax x hh; linarith [hx.1]))
        (by exact ⟨le_rfl, hwb.le⟩) (by exact ⟨hwb.le, le_rfl⟩)
      rw [hleft, hlocal v w hvδ hvu huw hwδ, hright, Finset.card_insert_of_notMem hus, Nat.cast_add, Nat.cast_one]
      ring
  exact aux events 1 (by norm_num) hinside hcontinuous hflip

end CurveComplex.LocalSurgery
