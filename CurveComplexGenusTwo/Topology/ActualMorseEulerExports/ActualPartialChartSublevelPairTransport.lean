import CurveComplexGenusTwo.Topology.ActualSimultaneousCriticalWindow.ActualPublicPairHomeomorphTransport

open Set CategoryTheory

/-- A literal partial chart transports bounded local sublevels of the ACTUAL
function to the ACTUAL coordinate pullback, without any quadratic equality input. -/
noncomputable def actual_partial_chart_sublevel_homeomorph
    {E : Type} [TopologicalSpace E] (c : OpenPartialHomeomorph E ℂ)
    (F : E → ℝ) (R h : ℝ) :
    {x : E | x ∈ c.source ∧ ‖c x‖ ≤ R ∧ F x ≤ h} ≃ₜ
      {z : ℂ | z ∈ c.target ∧ ‖z‖ ≤ R ∧ F (c.symm z) ≤ h} :=
  c.homeomorphOfImageSubsetSource
    (by intro x hx; exact hx.1)
    (by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨c.map_source hx.1, hx.2.1, by simpa only [c.left_inv hx.1] using hx.2.2⟩
      · intro hz
        exact ⟨c.symm z, ⟨c.symm.map_source hz.1,
          by simpa only [c.right_inv hz.1] using hz.2.1, hz.2.2⟩, c.right_inv hz.1⟩)
