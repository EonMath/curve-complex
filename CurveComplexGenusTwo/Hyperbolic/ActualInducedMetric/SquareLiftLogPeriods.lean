import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftLogHalfPlane

namespace CurveComplex.Hyperbolic
open Set Topology

noncomputable def logarithmDeckPeriod : ℂ := 2 * Real.pi * Complex.I

theorem logarithmDeckPeriod_re : logarithmDeckPeriod.re = 0 := by
  simp [logarithmDeckPeriod]

theorem logarithmDeckPeriod_ne_zero : logarithmDeckPeriod ≠ 0 := by
  simp [logarithmDeckPeriod, Real.pi_ne_zero]

theorem exp_add_logarithmDeckPeriod (z : ℂ) :
    Complex.exp (z + logarithmDeckPeriod) = Complex.exp z := by
  rw [Complex.exp_add]
  simp [logarithmDeckPeriod, Complex.exp_two_pi_mul_I]

theorem logLeftHalfPlane_add_period (A : ℝ) (z : ℂ) :
    z + logarithmDeckPeriod ∈ logLeftHalfPlane A ↔ z ∈ logLeftHalfPlane A := by
  change (z + logarithmDeckPeriod).re < A ↔ z.re < A
  rw [Complex.add_re, logarithmDeckPeriod_re, add_zero]

theorem continuous_exp_equal_integer_difference
    {X : Type*} [TopologicalSpace X] (U : Set X) (hU : IsPreconnected U) (hne : U.Nonempty)
    (F G : X → ℂ) (hF : ContinuousOn F U) (hG : ContinuousOn G U)
    (heq : ∀ z ∈ U, Complex.exp (F z) = Complex.exp (G z)) :
    ∃ n : ℤ, ∀ z ∈ U, F z = G z + n * logarithmDeckPeriod := by
  let T : Set ℂ := AddSubgroup.zmultiples logarithmDeckPeriod
  have hT : IsDiscrete T := by
    change IsDiscrete (AddSubgroup.zmultiples logarithmDeckPeriod : Set ℂ)
    exact isDiscrete_iff_discreteTopology.mpr (NormedSpace.discreteTopology_zmultiples _)
  have hmaps : MapsTo (fun z => F z - G z) U T := by
    intro z hz
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (heq z hz)
    apply AddSubgroup.mem_zmultiples_iff.mpr
    refine ⟨n, ?_⟩
    change n • logarithmDeckPeriod = F z - G z
    rw [zsmul_eq_mul]
    change n * logarithmDeckPeriod = F z - G z
    change F z = G z + n * logarithmDeckPeriod at hn
    rw [hn]
    ring
  obtain ⟨z0, hz0⟩ := hne
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp (heq z0 hz0)
  refine ⟨n, ?_⟩
  intro z hz
  have hconst := hU.constant_of_mapsTo hT (hF.sub hG) hmaps hz hz0
  change F z - G z = F z0 - G z0 at hconst
  change F z0 = G z0 + n * logarithmDeckPeriod at hn
  rw [hn] at hconst
  linear_combination hconst

theorem log_lift_has_integer_period
    (h : OpenPartialHomeomorph ℂ ℂ) (A : ℝ) (F : ℂ → ℂ)
    (hF : ContinuousOn F (logLeftHalfPlane A))
    (heq : ∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z)) :
    ∃ n : ℤ, ∀ z ∈ logLeftHalfPlane A,
      F (z + logarithmDeckPeriod) = F z + n * logarithmDeckPeriod := by
  apply continuous_exp_equal_integer_difference (logLeftHalfPlane A)
    (logLeftHalfPlane_convex A).isPreconnected (logLeftHalfPlane_nonempty A)
    (fun z => F (z + logarithmDeckPeriod)) F ?_ hF ?_
  · exact hF.comp (continuous_id.add continuous_const).continuousOn
      (fun z hz => (logLeftHalfPlane_add_period A z).mpr hz)
  · intro z hz
    rw [heq _ ((logLeftHalfPlane_add_period A z).mpr hz), heq _ hz,
      exp_add_logarithmDeckPeriod]

end CurveComplex.Hyperbolic
