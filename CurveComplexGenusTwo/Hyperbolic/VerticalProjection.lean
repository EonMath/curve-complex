import CurveComplexGenusTwo.Hyperbolic.VerticalGeodesic

namespace CurveComplex.Hyperbolic

private theorem vertical_scalar_minimum (v r y : ℝ)
    (hv : 0 < v) (_hr : 0 < r) (hy : 0 < y) :
    (2 * r ^ 2) / (2 * v * r) ≤ (r ^ 2 + y ^ 2) / (2 * v * y) ∧
      ((r ^ 2 + y ^ 2) / (2 * v * y) =
        (2 * r ^ 2) / (2 * v * r) → y = r) := by
  have hden : 2 * v * y ≠ 0 := by positivity
  have hdiff :
      (r ^ 2 + y ^ 2) / (2 * v * y) -
        (2 * r ^ 2) / (2 * v * r) =
      (y - r) ^ 2 / (2 * v * y) := by
    field_simp
    ring
  constructor
  · have hn : 0 ≤ (y - r) ^ 2 / (2 * v * y) := by positivity
    linarith
  · intro heq
    have hz : (y - r) ^ 2 / (2 * v * y) = 0 := by linarith
    have hs : (y - r) ^ 2 = 0 := (div_eq_zero_iff).mp hz |>.resolve_right hden
    nlinarith

private theorem upperHalfPlane_norm_pos (x : H2) : 0 < ‖(x : ℂ)‖ := by
  apply norm_pos_iff.mpr
  intro hx
  have him := congrArg Complex.im hx
  have hpos := x.im_pos
  simp at him
  linarith

noncomputable def verticalProjectionParameter (x : H2) : ℝ :=
  Real.log ‖(x : ℂ)‖

noncomputable def verticalProjection (x : H2) : H2 :=
  verticalPath (verticalProjectionParameter x)

theorem verticalProjectionParameter_continuous :
    Continuous verticalProjectionParameter := by
  apply continuous_iff_continuousAt.mpr
  intro x
  change ContinuousAt (fun x : H2 => Real.log ‖(x : ℂ)‖) x
  have hnorm : ContinuousAt (fun z : H2 => ‖(z : ℂ)‖) x :=
    (continuous_norm.comp UpperHalfPlane.continuous_coe).continuousAt
  exact ContinuousAt.comp (f := fun z : H2 => ‖(z : ℂ)‖)
    (Real.continuousAt_log (upperHalfPlane_norm_pos x).ne') hnorm

theorem verticalProjection_continuous : Continuous verticalProjection :=
  verticalPath_isometry.continuous.comp verticalProjectionParameter_continuous

private theorem cosh_dist_verticalPath (x : H2) (t : ℝ) :
    Real.cosh (dist x (verticalPath t)) =
      (x.re ^ 2 + x.im ^ 2 + (Real.exp t) ^ 2) /
        (2 * x.im * Real.exp t) := by
  rw [UpperHalfPlane.cosh_dist']
  simp [verticalPath]

theorem verticalProjection_nearest (x : H2) (t : ℝ) :
    dist x (verticalProjection x) ≤ dist x (verticalPath t) := by
  have hr : 0 < ‖(x : ℂ)‖ := upperHalfPlane_norm_pos x
  have hy : 0 < Real.exp t := Real.exp_pos t
  have hnorm : x.re ^ 2 + x.im ^ 2 = ‖(x : ℂ)‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm (x : ℂ)).symm
  have hc : Real.cosh (dist x (verticalProjection x)) ≤
      Real.cosh (dist x (verticalPath t)) := by
    rw [show verticalProjection x = verticalPath (verticalProjectionParameter x) from rfl,
      cosh_dist_verticalPath, cosh_dist_verticalPath]
    simp only [verticalProjectionParameter, Real.exp_log hr]
    rw [hnorm]
    simpa [two_mul] using
      (vertical_scalar_minimum x.im ‖(x : ℂ)‖ (Real.exp t)
        x.im_pos hr hy).1
  have hh := (Real.cosh_le_cosh).mp hc
  simpa [abs_of_nonneg dist_nonneg] using hh

theorem verticalProjection_unique (x : H2) (t : ℝ)
    (ht : dist x (verticalPath t) ≤ dist x (verticalProjection x)) :
    t = verticalProjectionParameter x := by
  have hr : 0 < ‖(x : ℂ)‖ := upperHalfPlane_norm_pos x
  have hy : 0 < Real.exp t := Real.exp_pos t
  have hnorm : x.re ^ 2 + x.im ^ 2 = ‖(x : ℂ)‖ ^ 2 := by
    simpa [Complex.normSq_apply, pow_two] using (Complex.sq_norm (x : ℂ)).symm
  have heq : dist x (verticalPath t) = dist x (verticalProjection x) :=
    le_antisymm ht (verticalProjection_nearest x t)
  have hc :
      (‖(x : ℂ)‖ ^ 2 + (Real.exp t) ^ 2) / (2 * x.im * Real.exp t) =
      (2 * ‖(x : ℂ)‖ ^ 2) / (2 * x.im * ‖(x : ℂ)‖) := by
    have hcosh := congrArg Real.cosh heq
    rw [cosh_dist_verticalPath, verticalProjection, cosh_dist_verticalPath] at hcosh
    simp only [verticalProjectionParameter, Real.exp_log hr] at hcosh
    rw [hnorm] at hcosh
    simpa [two_mul] using hcosh
  have hparam : Real.exp t = ‖(x : ℂ)‖ :=
    (vertical_scalar_minimum x.im ‖(x : ℂ)‖ (Real.exp t)
      x.im_pos hr hy).2 hc
  apply Real.exp_injective
  simpa [verticalProjectionParameter, Real.exp_log hr] using hparam

theorem verticalProjection_fixed (t : ℝ) :
    verticalProjection (verticalPath t) = verticalPath t := by
  have ht : dist (verticalPath t) (verticalPath t) ≤
      dist (verticalPath t) (verticalProjection (verticalPath t)) := by
    simp
  have hparam := verticalProjection_unique (verticalPath t) t ht
  rw [verticalProjection, ← hparam]

noncomputable def transportedVerticalProjection
    (e : H2 ≃ᵢ H2) (x : H2) : H2 :=
  e (verticalProjection (e.symm x))

theorem transportedVerticalProjection_continuous (e : H2 ≃ᵢ H2) :
    Continuous (transportedVerticalProjection e) := by
  exact e.continuous.comp
    (verticalProjection_continuous.comp e.symm.continuous)

private theorem transported_dist (e : H2 ≃ᵢ H2) (x y : H2) :
    dist x (e y) = dist (e.symm x) y := by
  simpa only [e.apply_symm_apply] using (e.dist_eq (e.symm x) y)

theorem transportedVerticalProjection_nearest
    (e : H2 ≃ᵢ H2) (x : H2) (t : ℝ) :
    dist x (transportedVerticalProjection e x) ≤
      dist x (e (verticalPath t)) := by
  have h := verticalProjection_nearest (e.symm x) t
  simpa only [transportedVerticalProjection, transported_dist] using h

theorem transportedVerticalProjection_unique
    (e : H2 ≃ᵢ H2) (x : H2) (t : ℝ)
    (ht : dist x (e (verticalPath t)) ≤
      dist x (transportedVerticalProjection e x)) :
    t = verticalProjectionParameter (e.symm x) := by
  apply verticalProjection_unique
  simpa only [transportedVerticalProjection, transported_dist] using ht

theorem transportedVerticalProjection_fixed
    (e : H2 ≃ᵢ H2) (t : ℝ) :
    transportedVerticalProjection e (e (verticalPath t)) =
      e (verticalPath t) := by
  simp [transportedVerticalProjection, verticalProjection_fixed]

theorem completeGeodesic_normalized_projection
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {D : IdealDisc B C} (g : CompleteGeodesic B C D)
    (e : H2 ≃ᵢ H2)
    (hpath : ∀ t, g.line.path t = e (verticalPath t)) :
    ∃ p : H2 → H2, Continuous p ∧
      ∀ x, (∃ t, p x = g.line.path t) ∧
        (∀ t, dist x (p x) ≤ dist x (g.line.path t)) ∧
        (∀ t, dist x (g.line.path t) ≤ dist x (p x) →
          g.line.path t = p x) := by
  refine ⟨transportedVerticalProjection e,
    transportedVerticalProjection_continuous e, ?_⟩
  intro x
  refine ⟨⟨verticalProjectionParameter (e.symm x), ?_⟩, ?_, ?_⟩
  · rw [hpath]
    rfl
  · intro t
    rw [hpath]
    exact transportedVerticalProjection_nearest e x t
  · intro t ht
    rw [hpath] at ht ⊢
    have heq := transportedVerticalProjection_unique e x t ht
    rw [heq]
    rfl

end CurveComplex.Hyperbolic
