import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftPuncturedProperties

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def extendedSquareLift (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  if z = 0 then 0 else puncturedSquareLift F z

@[simp]
theorem extendedSquareLift_zero (F : ℂ → ℂ) : extendedSquareLift F 0 = 0 := by
  simp [extendedSquareLift]

theorem extendedSquareLift_square (h : OpenPartialHomeomorph ℂ ℂ)
    (hzero : h 0 = 0) (A : ℝ) (F : ℂ → ℂ)
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z))
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) (Real.exp (A / 2))) :
    extendedSquareLift F z ^ 2 = h (z ^ 2) := by
  by_cases hz0 : z = 0
  · subst z
    simp [hzero]
  · rw [extendedSquareLift, if_neg hz0]
    exact puncturedSquareLift_square h A F heq z ⟨hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩

theorem extendedSquareLift_continuousAt_zero
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) (A : ℝ) (F : ℂ → ℂ)
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z)) :
    ContinuousAt (extendedSquareLift F) (0 : ℂ) := by
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp (h.continuousAt hsource) (ε ^ 2) (sq_pos_of_pos hε)
  let r := min (Real.exp (A / 2)) (min 1 δ)
  have hr : 0 < r := lt_min (Real.exp_pos _) (lt_min (by norm_num) hδ)
  refine ⟨r, hr, ?_⟩
  intro z hz
  rw [dist_zero_right] at hz
  have hzr : ‖z‖ < Real.exp (A / 2) := lt_of_lt_of_le hz (min_le_left _ _)
  have hz1 : ‖z‖ < 1 := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_left _ _))
  have hzδ : ‖z‖ < δ := lt_of_lt_of_le hz ((min_le_right _ _).trans (min_le_right _ _))
  have hzsquared : dist (z ^ 2) 0 < δ := by
    rw [dist_zero_right, norm_pow]
    nlinarith [norm_nonneg z]
  have hh := hbound hzsquared
  rw [hzero, dist_zero_right] at hh
  have hsq := extendedSquareLift_square h hzero A F heq z (by simpa only [Metric.mem_ball, dist_zero_right] using hzr)
  have hn : ‖extendedSquareLift F z‖ ^ 2 = ‖h (z ^ 2)‖ := by
    rw [← norm_pow, hsq]
  rw [extendedSquareLift_zero, dist_zero_right]
  nlinarith [norm_nonneg (extendedSquareLift F z)]

theorem extendedSquareLift_continuousOn_ball
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hF : ContinuousOn F (logLeftHalfPlane A))
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z))
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod) :
    ContinuousOn (extendedSquareLift F) (Metric.ball (0 : ℂ) (Real.exp (A / 2))) := by
  have hc : ContinuousOn (puncturedSquareLift F) (squareLiftPuncturedDisc A) :=
    squareLiftLogFormula_descends_continuously A F k hF hperiod
  intro z hz
  apply ContinuousAt.continuousWithinAt
  by_cases hz0 : z = 0
  · subst z
    exact extendedSquareLift_continuousAt_zero h hsource hzero A F heq
  · have hzV : z ∈ squareLiftPuncturedDisc A := ⟨hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
    have hp : ContinuousAt (puncturedSquareLift F) z :=
      (hc z hzV).continuousAt ((squareLiftPuncturedDisc_isOpen A).mem_nhds hzV)
    apply hp.congr_of_eventuallyEq
    filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz0] with w hw
    exact if_neg hw

theorem extendedSquareLift_neg (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hk : k = 1 ∨ k = -1)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) (Real.exp (A / 2))) :
    extendedSquareLift F (-z) = -extendedSquareLift F z := by
  by_cases hz0 : z = 0
  · subst z; simp
  · rw [extendedSquareLift, if_neg (neg_ne_zero.mpr hz0), extendedSquareLift, if_neg hz0]
    exact puncturedSquareLift_neg A F k hk hperiod z
      ⟨hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩

theorem extendedSquareLift_injective_on_ball
    (h : OpenPartialHomeomorph ℂ ℂ) (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hk : k = 1 ∨ k = -1)
    (hmaps : ∀ w ∈ logLeftHalfPlane A, Complex.exp w ∈ h.source)
    (heq : ∀ w ∈ logLeftHalfPlane A, Complex.exp (F w) = h (Complex.exp w))
    (hperiod : ∀ w ∈ logLeftHalfPlane A,
      F (w + logarithmDeckPeriod) = F w + k * logarithmDeckPeriod) :
    InjOn (extendedSquareLift F) (Metric.ball (0 : ℂ) (Real.exp (A / 2))) := by
  intro a ha b hb hab
  by_cases ha0 : a = 0 <;> by_cases hb0 : b = 0
  · exact ha0.trans hb0.symm
  · rw [ha0, extendedSquareLift_zero, extendedSquareLift, if_neg hb0] at hab
    exact False.elim (puncturedSquareLift_nonzero F b hab.symm)
  · rw [hb0, extendedSquareLift_zero, extendedSquareLift, if_neg ha0] at hab
    exact False.elim (puncturedSquareLift_nonzero F a hab)
  · rw [extendedSquareLift, if_neg ha0, extendedSquareLift, if_neg hb0] at hab
    exact puncturedSquareLift_injective_on_disc h A F k hk hmaps heq hperiod
      ⟨ha0, by simpa only [Metric.mem_ball, dist_zero_right] using ha⟩
      ⟨hb0, by simpa only [Metric.mem_ball, dist_zero_right] using hb⟩ hab

end CurveComplex.Hyperbolic
