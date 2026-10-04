import CurveComplexGenusTwo.Topology.ActualFareyClassification.ActualHorizontalFiberSidePreservation

open Set Topology Schoenflies CurveComplex

/-- A supported periodic operation whose actual open support lies strictly
inside one fundamental strip fixes EVERY original reference-grid point at
EVERY time. No puncture fixing is inferred from this separate reference law. -/
theorem actual_band_supported_operation_fixes_horizontal_grid
    (T c : ℝ) (hT : 0 < T) (U : Set Plane)
    (hU : ∀ w ∈ U, c < w 1 ∧ w 1 < c+T)
    (H : AmbientIsotopy Plane)
    (hFix : ∀ t z, z ∉ ⋃ i : ℤ × ℤ,
      (fun w : Plane => w + Plane.mk ((i.1 : ℝ)*T) ((i.2 : ℝ)*T)) '' U → H.map (t,z) = z) :
    ∀ t (k : ℤ) (z : Plane), z 1 = c + (k : ℝ)*T → H.map (t,z) = z := by
  intro t k z hz
  apply hFix
  intro hm
  obtain ⟨i,w,hw,he⟩ := mem_iUnion.mp hm
  have hx := congrArg (fun q : Plane => q 1) he
  change w 1 + (i.2 : ℝ)*T = z 1 at hx
  rw [hz] at hx
  have hBounds := hU w hw
  rcases le_total k i.2 with hle | hle
  · have hleR : (k : ℝ) ≤ (i.2 : ℝ) := by exact_mod_cast hle
    have hh := mul_le_mul_of_nonneg_right hleR hT.le
    linarith [hBounds.1]
  · by_cases heq : i.2 = k
    · subst k
      linarith [hBounds.1]
    · have hStep : i.2+1 ≤ k := by omega
      have hStepR : (i.2 : ℝ)+1 ≤ (k : ℝ) := by exact_mod_cast hStep
      have hh := mul_le_mul_of_nonneg_right hStepR hT.le
      linarith [hBounds.2]

#print axioms actual_band_supported_operation_fixes_horizontal_grid
