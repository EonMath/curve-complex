import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftLogControl

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def squareLiftLogFormula (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  Complex.exp (F (2 * w) / 2)

theorem squareLiftLogFormula_square (h : OpenPartialHomeomorph ℂ ℂ)
    (A : ℝ) (F : ℂ → ℂ)
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z))
    (w : ℂ) (hw : w ∈ logLeftHalfPlane (A / 2)) :
    squareLiftLogFormula F w ^ 2 = h (Complex.exp w ^ 2) := by
  have h2w : 2 * w ∈ logLeftHalfPlane A := by
    change w.re < A / 2 at hw
    change (2 * w).re < A
    norm_num [Complex.mul_re]
    linarith
  rw [squareLiftLogFormula, ← Complex.exp_nat_mul]
  norm_num only [Nat.cast_ofNat]
  have harg : (2 : ℂ) * (F (2 * w) / 2) = F (2 * w) := by ring
  rw [harg, heq _ h2w]
  congr 1
  convert Complex.exp_nat_mul w 2 using 1 <;> norm_num

theorem squareLiftLogFormula_period (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (w : ℂ) (hw : w ∈ logLeftHalfPlane (A / 2)) (n : ℤ) :
    squareLiftLogFormula F (w + n * logarithmDeckPeriod) = squareLiftLogFormula F w := by
  have h2w : 2 * w ∈ logLeftHalfPlane A := by
    change w.re < A / 2 at hw
    change (2 * w).re < A
    norm_num [Complex.mul_re]
    linarith
  have harg : (2 : ℂ) * (w + n * logarithmDeckPeriod) =
      2 * w + ((2 * n : ℤ) : ℂ) * logarithmDeckPeriod := by push_cast; ring
  rw [squareLiftLogFormula, squareLiftLogFormula, harg,
    log_lift_integer_period_shift A F k hperiod (2 * w) h2w (2 * n)]
  have harg' : (F (2 * w) + ((2 * n : ℤ) : ℂ) * k * logarithmDeckPeriod) / 2 =
      F (2 * w) / 2 + ((n * k : ℤ) : ℂ) * logarithmDeckPeriod := by push_cast; ring
  rw [harg', Complex.exp_add]
  have he : Complex.exp (((n * k : ℤ) : ℂ) * logarithmDeckPeriod) = 1 :=
    Complex.exp_eq_one_iff.mpr ⟨n * k, rfl⟩
  rw [he, mul_one]

theorem squareLiftLogFormula_equal_exp_representatives (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (w v : ℂ) (hw : w ∈ logLeftHalfPlane (A / 2))
    (heq : Complex.exp w = Complex.exp v) :
    squareLiftLogFormula F w = squareLiftLogFormula F v := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp heq.symm
  change v = w + n * logarithmDeckPeriod at hn
  rw [hn]
  exact (squareLiftLogFormula_period A F k hperiod w hw n).symm

theorem squareLiftLogFormula_negation_period (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hk : k = 1 ∨ k = -1)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (w : ℂ) (hw : w ∈ logLeftHalfPlane (A / 2)) :
    squareLiftLogFormula F (w + logarithmDeckPeriod / 2) = -squareLiftLogFormula F w := by
  have h2w : 2 * w ∈ logLeftHalfPlane A := by
    change w.re < A / 2 at hw
    change (2 * w).re < A
    norm_num [Complex.mul_re]
    linarith
  have harg : (2 : ℂ) * (w + logarithmDeckPeriod / 2) = 2 * w + logarithmDeckPeriod := by ring
  rw [squareLiftLogFormula, squareLiftLogFormula, harg, hperiod _ h2w]
  rw [add_div, Complex.exp_add]
  have he : Complex.exp ((k : ℂ) * logarithmDeckPeriod / 2) = -1 := by
    rcases hk with rfl | rfl
    · simp only [Int.cast_one]
      have harg : (1 : ℂ) * logarithmDeckPeriod / 2 = Real.pi * Complex.I := by
        unfold logarithmDeckPeriod; ring
      rw [harg]
      exact Complex.exp_pi_mul_I
    · have harg : (-1 : ℂ) * logarithmDeckPeriod / 2 = -(Real.pi * Complex.I) := by
        unfold logarithmDeckPeriod; ring
      simpa only [Int.cast_neg, Int.cast_one, harg] using Complex.exp_neg_pi_mul_I
  rw [he, mul_neg_one]

end CurveComplex.Hyperbolic
