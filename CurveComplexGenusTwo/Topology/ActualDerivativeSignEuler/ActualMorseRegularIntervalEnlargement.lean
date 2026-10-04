import CurveComplexGenusTwo.Topology.ActualDerivativeSignEuler.ActualMorseRegularValueWindows

open Set

theorem actual_finite_critical_value_regular_closed_interval_enlargement
    {E : Type*} (F : E → ℝ) (Z : Finset E) (a b : ℝ) (hab : a ≤ b)
    (havoid : ∀ x ∈ Z, F x ∉ Icc a b) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x ∈ Z, F x ∉ Icc (a - δ) (b + δ) := by
  obtain ⟨r, hr, hra⟩ := actual_finite_critical_value_regular_window F Z a (by
    intro x hx heq
    apply havoid x hx
    rw [heq]
    exact ⟨le_rfl, hab⟩)
  obtain ⟨s, hs, hsb⟩ := actual_finite_critical_value_regular_window F Z b (by
    intro x hx heq
    apply havoid x hx
    rw [heq]
    exact ⟨hab, le_rfl⟩)
  let δ : ℝ := min r s / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hdr : δ < r := by
    dsimp [δ]
    linarith [min_le_left r s, lt_min hr hs]
  have hds : δ < s := by
    dsimp [δ]
    linarith [min_le_right r s, lt_min hr hs]
  refine ⟨δ, hδ, ?_⟩
  intro x hx hmem
  by_cases hxa : F x < a
  · have hh := hra x hx
    rw [abs_of_neg (sub_neg.mpr hxa)] at hh
    linarith [hmem.1]
  · have hxb : b < F x := by
      by_contra hnot
      exact havoid x hx ⟨le_of_not_gt hxa, le_of_not_gt hnot⟩
    have hh := hsb x hx
    rw [abs_of_pos (sub_pos.mpr hxb)] at hh
    linarith [hmem.2]
