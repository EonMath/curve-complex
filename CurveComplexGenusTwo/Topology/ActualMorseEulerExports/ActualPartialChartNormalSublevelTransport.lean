import CurveComplexGenusTwo.Topology.ActualMorseEulerExports.ActualPartialChartSublevelPairTransport

open Set CategoryTheory

/-- Identifies the actual chart pullback with a proved local normal form;
the coordinate ball lies in the actual target. The function q is literal. -/
theorem actual_partial_chart_normal_sublevel_set_eq
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (q : ℂ → ℝ) (R h : ℝ)
    (hball : Metric.closedBall (0 : ℂ) R ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + q (c x)) :
    {z : ℂ | z ∈ c.target ∧ ‖z‖ ≤ R ∧ F (c.symm z) ≤ F p + h} =
      {z : ℂ | ‖z‖ ≤ R ∧ q z ≤ h} := by
  ext z
  constructor
  · intro hz
    have he := hnormal (c.symm z) (c.symm.map_source hz.1)
    rw [c.right_inv hz.1] at he
    exact ⟨hz.2.1, by linarith [hz.2.2]⟩
  · intro hz
    have hzt : z ∈ c.target := hball (by simpa only [Metric.mem_closedBall, dist_zero_right] using hz.1)
    have he := hnormal (c.symm z) (c.symm.map_source hzt)
    rw [c.right_inv hzt] at he
    exact ⟨hzt, hz.1, by linarith [hz.2]⟩

noncomputable def actual_partial_chart_normal_sublevel_homeomorph
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (q : ℂ → ℝ) (R h : ℝ)
    (hball : Metric.closedBall (0 : ℂ) R ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + q (c x)) :
    {x : E | x ∈ c.source ∧ ‖c x‖ ≤ R ∧ F x ≤ F p + h} ≃ₜ
      {z : ℂ | ‖z‖ ≤ R ∧ q z ≤ h} :=
  (actual_partial_chart_sublevel_homeomorph c F R (F p + h)).trans
    (Homeomorph.setCongr (actual_partial_chart_normal_sublevel_set_eq
      c F p q R h hball hnormal))

theorem actual_partial_chart_normal_sublevel_lower_membership
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (q : ℂ → ℝ) (R h a : ℝ)
    (hball : Metric.closedBall (0 : ℂ) R ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + q (c x))
    (x : {x : E | x ∈ c.source ∧ ‖c x‖ ≤ R ∧ F x ≤ F p + h}) :
    F x.1 ≤ F p + a ↔
      q ((actual_partial_chart_normal_sublevel_homeomorph c F p q R h hball hnormal x).1) ≤ a := by
  change F x.1 ≤ F p + a ↔ q (c x.1) ≤ a
  rw [hnormal x.1 x.2.1]
  exact add_le_add_iff_left (F p)

set_option backward.isDefEq.respectTransparency false in
theorem actual_partial_chart_normal_sublevel_pair_relativeHomology_isIso
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (p : E) (q : ℂ → ℝ) (R h a : ℝ)
    (hball : Metric.closedBall (0 : ℂ) R ⊆ c.target)
    (hnormal : ∀ x ∈ c.source, F x = F p + q (c x)) (n : ℕ) :
    let X := {x : E | x ∈ c.source ∧ ‖c x‖ ≤ R ∧ F x ≤ F p + h}
    let Y := {z : ℂ | ‖z‖ ≤ R ∧ q z ≤ h}
    let A : Set X := {x | F x.1 ≤ F p + a}
    let B : Set Y := {z | q z.1 ≤ a}
    IsIso (CurveComplexGenusTwo.CWHurewicz.pairRelativeHomologyMap A B
      ⟨actual_partial_chart_normal_sublevel_homeomorph c F p q R h hball hnormal,
        (actual_partial_chart_normal_sublevel_homeomorph c F p q R h hball hnormal).continuous⟩
      (fun x hx => (actual_partial_chart_normal_sublevel_lower_membership
        c F p q R h a hball hnormal x).mp hx) n) := by
  dsimp only
  apply actual_pairRelativeHomologyMap_homeomorph_isIso _ _ _ _
    (actual_partial_chart_normal_sublevel_homeomorph c F p q R h hball hnormal)
  intro x
  exact actual_partial_chart_normal_sublevel_lower_membership c F p q R h a hball hnormal x

