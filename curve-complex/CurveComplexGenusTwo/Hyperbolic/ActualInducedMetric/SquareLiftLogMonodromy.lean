import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.SquareLiftLogControl

namespace CurveComplex.Hyperbolic
open Set Topology

theorem local_plane_homeomorphism_log_lift_unit_period
    (h : OpenPartialHomeomorph ℂ ℂ) (hsource : (0 : ℂ) ∈ h.source)
    (hzero : h 0 = 0) :
    ∃ A : ℝ, ∃ F : ℂ → ℂ, ∃ k : ℤ, (k = 1 ∨ k = -1) ∧
      ContinuousOn F (logLeftHalfPlane A) ∧
      (∀ z ∈ logLeftHalfPlane A, Complex.exp z ∈ h.source) ∧
      (∀ z ∈ logLeftHalfPlane A, Complex.exp (F z) = h (Complex.exp z)) ∧
      ∀ z ∈ logLeftHalfPlane A,
        F (z + logarithmDeckPeriod) = F z + k * logarithmDeckPeriod := by
  obtain ⟨A, F, hF, hmapsF, hnonzeroF, heqF⟩ :=
    local_plane_homeomorphism_log_lift h hsource hzero
  obtain ⟨k, hperiodF⟩ := log_lift_has_integer_period h A F hF heqF
  have htarget : (0 : ℂ) ∈ h.target := by
    rw [← hzero]
    exact h.map_source hsource
  have hinvzero : h.symm (0 : ℂ) = 0 := by
    calc
      _ = h.symm (h 0) := congrArg h.symm hzero.symm
      _ = 0 := h.left_inv hsource
  obtain ⟨B, G, hG, hmapsG, hnonzeroG, heqG⟩ :=
    local_plane_homeomorphism_log_lift h.symm htarget hinvzero
  obtain ⟨k', hperiodG⟩ := log_lift_has_integer_period h.symm B G hG heqG
  obtain ⟨C, hCA, hFC⟩ := log_lift_maps_deep_halfPlane h hsource hzero A B F heqF
  have hCAset : logLeftHalfPlane C ⊆ logLeftHalfPlane A := fun z hz => lt_trans hz hCA
  have hcomp : ContinuousOn (fun z => G (F z)) (logLeftHalfPlane C) :=
    hG.comp (hF.mono hCAset) hFC
  have hcompExp : ∀ z ∈ logLeftHalfPlane C, Complex.exp (G (F z)) = Complex.exp z := by
    intro z hz
    rw [heqG _ (hFC hz), heqF _ (hCAset hz)]
    exact h.left_inv (hmapsF z (hCAset hz))
  obtain ⟨j, hidentity⟩ := continuous_exp_equal_integer_difference (logLeftHalfPlane C)
    (logLeftHalfPlane_convex C).isPreconnected (logLeftHalfPlane_nonempty C)
    (fun z => G (F z)) id hcomp continuousOn_id hcompExp
  obtain ⟨z, hz⟩ := logLeftHalfPlane_nonempty C
  have hzs : z + logarithmDeckPeriod ∈ logLeftHalfPlane C :=
    (logLeftHalfPlane_add_period C z).mpr hz
  have hid0 := hidentity z hz
  have hid1 := hidentity (z + logarithmDeckPeriod) hzs
  change G (F z) = z + j * logarithmDeckPeriod at hid0
  change G (F (z + logarithmDeckPeriod)) = z + logarithmDeckPeriod + j * logarithmDeckPeriod at hid1
  rw [hperiodF z (hCAset hz), log_lift_integer_period_shift B G k' hperiodG (F z) (hFC hz) k,
    hid0] at hid1
  have hmul : ((k * k' : ℤ) : ℂ) * logarithmDeckPeriod = (1 : ℂ) * logarithmDeckPeriod := by
    push_cast
    linear_combination hid1
  have hkcomplex : ((k * k' : ℤ) : ℂ) = 1 := mul_right_cancel₀ logarithmDeckPeriod_ne_zero hmul
  have hkint : k * k' = 1 := by exact_mod_cast hkcomplex
  have hkunit : k = 1 ∨ k = -1 := Int.isUnit_iff.mp (IsUnit.of_mul_eq_one k' hkint)
  exact ⟨A, F, k, hkunit, hF, hmapsF, heqF, hperiodF⟩

end CurveComplex.Hyperbolic
