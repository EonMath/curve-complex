import CurveComplexGenusTwo.Hyperbolic.VerticalGeodesic

namespace CurveComplex.Hyperbolic

theorem re_eq_of_dist_log_im_eq (z w : H2)
    (h : dist (Real.log z.im) (Real.log w.im) = dist z w) :
    z.re = w.re := by
  let z₀ : H2 := UpperHalfPlane.mk ⟨0, z.im⟩ z.im_pos
  let w₀ : H2 := UpperHalfPlane.mk ⟨0, w.im⟩ w.im_pos
  have h₀ : dist z₀ w₀ = dist (Real.log z.im) (Real.log w.im) := by
    exact UpperHalfPlane.dist_of_re_eq rfl
  have hc : Real.cosh (dist z₀ w₀) = Real.cosh (dist z w) := by
    rw [h₀, h]
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc
  have hd : 2 * z.im * w.im ≠ 0 := by positivity
  dsimp [z₀, w₀] at hc
  simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] at hc
  have heq : z.im ^ 2 + w.im ^ 2 =
      (z.re - w.re) ^ 2 + z.im ^ 2 + w.im ^ 2 :=
    (div_left_inj' hd).mp hc
  nlinarith [sq_nonneg (z.re - w.re)]

theorem dist_log_im_eq_iff_re_eq (z w : H2) :
    dist (Real.log z.im) (Real.log w.im) = dist z w ↔ z.re = w.re := by
  constructor
  · exact re_eq_of_dist_log_im_eq z w
  · intro h
    rw [UpperHalfPlane.dist_of_re_eq h]

theorem eq_verticalPath_of_two_distances (z : H2) (t : ℝ)
    (h0 : dist (verticalPath 0) z =
      dist (verticalPath 0) (verticalPath t))
    (h1 : dist (verticalPath 1) z =
      dist (verticalPath 1) (verticalPath t)) :
    z = verticalPath t := by
  have hc0 := congrArg Real.cosh h0
  have hc1 := congrArg Real.cosh h1
  rw [UpperHalfPlane.cosh_dist', UpperHalfPlane.cosh_dist'] at hc0 hc1
  simp only [verticalPath, UpperHalfPlane.mk_re, UpperHalfPlane.mk_im,
    Real.exp_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_sub,
    neg_sq, zero_add, mul_one] at hc0 hc1
  have hz : 0 < z.im := z.im_pos
  have ha : 0 < Real.exp t := Real.exp_pos t
  have hb : 1 < Real.exp (1 : ℝ) := Real.one_lt_exp_iff.mpr (by norm_num)
  have h0eq : Real.exp t * (z.re ^ 2 + z.im ^ 2 + 1) =
      z.im * (1 + (Real.exp t) ^ 2) := by
    field_simp at hc0
    nlinarith [hc0]
  have h1eq : Real.exp t * (z.re ^ 2 + z.im ^ 2 + (Real.exp (1 : ℝ)) ^ 2) =
      z.im * ((Real.exp (1 : ℝ)) ^ 2 + (Real.exp t) ^ 2) := by
    field_simp at hc1
    nlinarith [hc1]
  have him : z.im = Real.exp t := by
    have hfactor : ((Real.exp (1 : ℝ)) ^ 2 - 1) * (Real.exp t - z.im) = 0 := by
      nlinarith [h0eq, h1eq]
    have hpos : 0 < (Real.exp (1 : ℝ)) ^ 2 - 1 := by nlinarith
    nlinarith
  have hre : z.re = 0 := by
    rw [him] at h0eq
    have hp : Real.exp t * z.re ^ 2 = 0 := by nlinarith [h0eq]
    have hs : z.re ^ 2 = 0 := (mul_eq_zero.mp hp).resolve_left ha.ne'
    nlinarith
  apply UpperHalfPlane.ext_re_im
  · simpa [verticalPath] using hre
  · simpa [verticalPath] using him

theorem isometry_eq_vertical_of_values (f : ℝ → H2) (hf : Isometry f)
    (h0 : f 0 = verticalPath 0) (h1 : f 1 = verticalPath 1) :
    ∀ t, f t = verticalPath t := by
  intro t
  apply eq_verticalPath_of_two_distances
  · calc
      dist (verticalPath 0) (f t) = dist (f 0) (f t) := by rw [h0]
      _ = dist (0 : ℝ) t := hf.dist_eq 0 t
      _ = dist (verticalPath 0) (verticalPath t) :=
        (verticalPath_isometry.dist_eq 0 t).symm
  · calc
      dist (verticalPath 1) (f t) = dist (f 1) (f t) := by rw [h1]
      _ = dist (1 : ℝ) t := hf.dist_eq 1 t
      _ = dist (verticalPath 1) (verticalPath t) :=
        (verticalPath_isometry.dist_eq 1 t).symm

theorem completeGeodesic_normalized_of_pair_alignment
    {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]
    {D : IdealDisc B C} (g : CompleteGeodesic B C D)
    (e : H2 ≃ᵢ H2)
    (h0 : e (verticalPath 0) = g.line.path 0)
    (h1 : e (verticalPath 1) = g.line.path 1) :
    ∀ t, g.line.path t = e (verticalPath t) := by
  have hf : Isometry (fun t : ℝ => e.symm (g.line.path t)) :=
    e.symm.isometry.comp g.isometry
  have hf0 : e.symm (g.line.path 0) = verticalPath 0 := by
    rw [← h0, e.symm_apply_apply]
  have hf1 : e.symm (g.line.path 1) = verticalPath 1 := by
    rw [← h1, e.symm_apply_apply]
  intro t
  have ht := isometry_eq_vertical_of_values _ hf hf0 hf1 t
  simpa only [e.apply_symm_apply] using congrArg e ht

end CurveComplex.Hyperbolic
