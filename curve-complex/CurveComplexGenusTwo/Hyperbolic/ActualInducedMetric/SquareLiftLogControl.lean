import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftLogPeriods

namespace CurveComplex.Hyperbolic
open Set Topology

theorem log_lift_maps_deep_halfPlane
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) (A B : ℝ) (F : ℂ → ℂ)
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z)) :
    ∃ C : ℝ, C < A ∧ MapsTo F (logLeftHalfPlane C) (logLeftHalfPlane B) := by
  obtain ⟨δ, hδ, hbound⟩ := Metric.continuousAt_iff.mp (h.continuousAt hsource)
    (Real.exp B) (Real.exp_pos B)
  let C := min A (Real.log δ) - 1
  have hCA : C < A := by dsimp [C]; have := min_le_left A (Real.log δ); linarith
  have hCδ : C < Real.log δ := by dsimp [C]; have := min_le_right A (Real.log δ); linarith
  refine ⟨C, hCA, ?_⟩
  intro z hz
  have hzA : z ∈ logLeftHalfPlane A := lt_trans hz hCA
  have hzδ : dist (Complex.exp z) 0 < δ := by
    rw [dist_zero_right, Complex.norm_exp]
    have hlog : z.re < Real.log δ := lt_trans hz hCδ
    have he := Real.exp_lt_exp.mpr hlog
    rwa [Real.exp_log hδ] at he
  have hb := hbound hzδ
  rw [hzero, dist_zero_right, ← heq z hzA, Complex.norm_exp] at hb
  exact Real.exp_lt_exp.mp hb

theorem logLeftHalfPlane_add_int_period (A : ℝ) (z : ℂ) (n : ℤ) :
    z + n * logarithmDeckPeriod ∈ logLeftHalfPlane A ↔ z ∈ logLeftHalfPlane A := by
  change (z + n * logarithmDeckPeriod).re < A ↔ z.re < A
  simp [Complex.add_re, Complex.mul_re, logarithmDeckPeriod]

theorem log_lift_integer_period_shift (A : ℝ) (F : ℂ → ℂ) (k : ℤ)
    (hperiod : ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod)
    (z : ℂ) (hz : z ∈ logLeftHalfPlane A) (n : ℤ) :
    F (z + n * logarithmDeckPeriod) = F z + n * k * logarithmDeckPeriod := by
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    push_cast at ih
    have hm : z + (n : ℂ) * logarithmDeckPeriod ∈ logLeftHalfPlane A :=
      (logLeftHalfPlane_add_int_period A z n).mpr hz
    have he := hperiod _ hm
    have harg : z + ((n + 1 : ℤ) : ℂ) * logarithmDeckPeriod =
        (z + (n : ℂ) * logarithmDeckPeriod) + logarithmDeckPeriod := by push_cast; ring
    rw [harg, he, ih]
    push_cast
    ring
  | pred n ih =>
    have hm : z + ((-(n + 1 : ℤ) : ℤ) : ℂ) * logarithmDeckPeriod ∈ logLeftHalfPlane A :=
      (logLeftHalfPlane_add_int_period A z (-(n + 1))).mpr hz
    have he := hperiod _ hm
    have harg : z + ((-(n + 1 : ℤ) : ℤ) : ℂ) * logarithmDeckPeriod + logarithmDeckPeriod =
        z + ((-n : ℤ) : ℂ) * logarithmDeckPeriod := by push_cast; ring
    rw [harg, ih] at he
    push_cast at he ⊢
    simp only [sub_eq_add_neg, neg_add] at he ⊢
    linear_combination -he

end CurveComplex.Hyperbolic
