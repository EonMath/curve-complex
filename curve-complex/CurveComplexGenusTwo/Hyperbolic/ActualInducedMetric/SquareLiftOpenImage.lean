import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftExtension

namespace CurveComplex.Hyperbolic
open Set Topology

theorem square_lift_symmetric_image_preimage
    (h : OpenPartialHomeomorph ℂ ℂ) (g : ℂ → ℂ) (U : Set ℂ)
    (hneg : ∀ z ∈ U, -z ∈ U ∧ g (-z) = -g z)
    (hsquare : ∀ z ∈ U, g z ^ 2 = h (z ^ 2)) :
    g '' U = (fun z : ℂ => z ^ 2) ⁻¹' (h '' ((fun z : ℂ => z ^ 2) '' U)) := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z ^ 2, ⟨z, hz, rfl⟩, (hsquare z hz).symm⟩
  · rintro ⟨v, ⟨z, hz, rfl⟩, heq⟩
    have hsq : w ^ 2 = g z ^ 2 := heq.symm.trans (hsquare z hz).symm
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hw | hw
    · exact ⟨z, hz, hw.symm⟩
    · obtain ⟨hnz, hgz⟩ := hneg z hz
      exact ⟨-z, hnz, hgz.trans hw.symm⟩

theorem square_lift_symmetric_image_isOpen
    (h : OpenPartialHomeomorph ℂ ℂ) (g : ℂ → ℂ) (U : Set ℂ)
    (hU : IsOpen U)
    (hmem : ∀ z ∈ U, z ^ 2 ∈ h.source)
    (hneg : ∀ z ∈ U, -z ∈ U ∧ g (-z) = -g z)
    (hsquare : ∀ z ∈ U, g z ^ 2 = h (z ^ 2)) : IsOpen (g '' U) := by
  rw [square_lift_symmetric_image_preimage h g U hneg hsquare]
  have hsub : (fun z : ℂ => z ^ 2) '' U ⊆ h.source := by
    rintro w ⟨z, hz, rfl⟩
    exact hmem z hz
  have hopen := h.isOpen_image_of_subset_source
    ((Complex.isOpenQuotientMap_pow 2).isOpenMap U hU) hsub
  exact hopen.preimage (continuous_id.pow 2)

theorem extendedSquareLift_square_source
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (A : ℝ) (hmaps : ∀ w ∈ logLeftHalfPlane A, Complex.exp w ∈ h.source)
    (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) (Real.exp (A / 2))) : z ^ 2 ∈ h.source := by
  by_cases hz0 : z = 0
  · subst z; simpa using hsource
  · have hw : Complex.log z ∈ logLeftHalfPlane (A / 2) :=
      log_mem_squareLiftHalfPlane A z ⟨hz0, by simpa only [Metric.mem_ball, dist_zero_right] using hz⟩
    have h2w : 2 * Complex.log z ∈ logLeftHalfPlane A := by
      change (Complex.log z).re < A / 2 at hw
      change (2 * Complex.log z).re < A
      norm_num [Complex.mul_re]
      linarith
    have he := hmaps _ h2w
    have hex : Complex.exp (2 * Complex.log z) = z ^ 2 := by
      calc
        _ = (Complex.exp (Complex.log z)) ^ 2 := by simpa using Complex.exp_nat_mul (Complex.log z) 2
        _ = z ^ 2 := by rw [Complex.exp_log hz0]
    rwa [hex] at he

end CurveComplex.Hyperbolic
