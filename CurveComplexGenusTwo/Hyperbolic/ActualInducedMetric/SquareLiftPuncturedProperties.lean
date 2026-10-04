import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftPuncturedDomain

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def puncturedSquareLift (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  squareLiftLogFormula F (Complex.log z)

theorem puncturedSquareLift_nonzero (F : ℂ → ℂ) (z : ℂ) : puncturedSquareLift F z ≠ 0 :=
  Complex.exp_ne_zero _

theorem puncturedSquareLift_square (h : OpenPartialHomeomorph ℂ ℂ)
    (A : ℝ) (F : ℂ → ℂ)
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z))
    (z : ℂ) (hz : z ∈ squareLiftPuncturedDisc A) :
    puncturedSquareLift F z ^ 2 = h (z ^ 2) := by
  have he := squareLiftLogFormula_square h A F heq (Complex.log z) (log_mem_squareLiftHalfPlane A z hz)
  rwa [Complex.exp_log hz.1] at he

theorem squareLiftPuncturedDisc_neg (A : ℝ) (z : ℂ) :
    -z ∈ squareLiftPuncturedDisc A ↔ z ∈ squareLiftPuncturedDisc A := by
  simp [squareLiftPuncturedDisc]

theorem exp_half_logarithmDeckPeriod : Complex.exp (logarithmDeckPeriod / 2) = -1 := by
  have he : logarithmDeckPeriod / 2 = Real.pi * Complex.I := by unfold logarithmDeckPeriod; ring
  rw [he]
  exact Complex.exp_pi_mul_I

theorem puncturedSquareLift_neg (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hk : k = 1 ∨ k = -1)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (z : ℂ) (hz : z ∈ squareLiftPuncturedDisc A) :
    puncturedSquareLift F (-z) = -puncturedSquareLift F z := by
  let w := Complex.log z
  have hw : w ∈ logLeftHalfPlane (A / 2) := log_mem_squareLiftHalfPlane A z hz
  have hwp : w + logarithmDeckPeriod / 2 ∈ logLeftHalfPlane (A / 2) := by
    change (w + logarithmDeckPeriod / 2).re < A / 2
    have hp : (logarithmDeckPeriod / 2).re = 0 := by simp [logarithmDeckPeriod]
    rw [Complex.add_re, hp, add_zero]
    exact hw
  have he : Complex.exp (w + logarithmDeckPeriod / 2) = -z := by
    rw [Complex.exp_add, exp_half_logarithmDeckPeriod, mul_neg_one]
    exact congrArg Neg.neg (Complex.exp_log hz.1)
  have heq : Complex.exp (w + logarithmDeckPeriod / 2) = Complex.exp (Complex.log (-z)) := by
    rw [Complex.exp_log (neg_ne_zero.mpr hz.1)]
    exact he
  change squareLiftLogFormula F (Complex.log (-z)) = -squareLiftLogFormula F w
  rw [← squareLiftLogFormula_equal_exp_representatives A F k hperiod
    (w + logarithmDeckPeriod / 2) (Complex.log (-z)) hwp heq]
  exact squareLiftLogFormula_negation_period A F k hk hperiod w hw

theorem puncturedSquareLift_injective_on_disc
    (h : OpenPartialHomeomorph ℂ ℂ) (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hk : k = 1 ∨ k = -1)
    (hmaps : ∀ w ∈ logLeftHalfPlane A, Complex.exp w ∈ h.source)
    (heq : ∀ w ∈ logLeftHalfPlane A, Complex.exp (F w) = h (Complex.exp w))
    (hperiod : ∀ w ∈ logLeftHalfPlane A,
      F (w + logarithmDeckPeriod) = F w + k * logarithmDeckPeriod) :
    InjOn (puncturedSquareLift F) (squareLiftPuncturedDisc A) := by
  have hsqmem (z : ℂ) (hz : z ∈ squareLiftPuncturedDisc A) : z ^ 2 ∈ h.source := by
    have hw := log_mem_squareLiftHalfPlane A z hz
    have h2w : 2 * Complex.log z ∈ logLeftHalfPlane A := by
      change (Complex.log z).re < A / 2 at hw
      change (2 * Complex.log z).re < A
      norm_num [Complex.mul_re]
      linarith
    have he := hmaps _ h2w
    have hExp : Complex.exp (2 * Complex.log z) = z ^ 2 := by
      calc
        _ = (Complex.exp (Complex.log z)) ^ 2 := by simpa using Complex.exp_nat_mul (Complex.log z) 2
        _ = z ^ 2 := by rw [Complex.exp_log hz.1]
    rwa [hExp] at he
  intro a ha b hb hab
  have hs : a ^ 2 = b ^ 2 := h.injOn (hsqmem a ha) (hsqmem b hb)
    (by rw [← puncturedSquareLift_square h A F heq a ha,
      ← puncturedSquareLift_square h A F heq b hb, hab])
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
  · exact he
  · have hg := puncturedSquareLift_neg A F k hk hperiod b hb
    rw [he] at hab
    rw [hg] at hab
    have hz : puncturedSquareLift F b = 0 := by linear_combination -hab / 2
    exact False.elim (puncturedSquareLift_nonzero F b hz)

end CurveComplex.Hyperbolic
