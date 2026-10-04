import Mathlib

namespace CurveComplex.CapBandGeometry

/-- Incidence matrix of the literal four overlap windows: all four land in
the square/collars component; windows 0,1 land in the first middle band,
and windows 2,3 in the second. The minus signs are MV's second inclusion. -/
def bandIncidence : (Fin 4 → ℤ) →ₗ[ℤ] ℤ × (Fin 2 → ℤ) where
  toFun x := (x 0 + x 1 + x 2 + x 3,
    ![-(x 0 + x 1), -(x 2 + x 3)])
  map_add' := by
    intros
    apply Prod.ext
    · simp; ring
    · ext i; fin_cases i <;> simp <;> ring
  map_smul' := by
    intros
    apply Prod.ext
    · simp; ring
    · ext i; fin_cases i <;> simp <;> ring

/-- Two actual signed difference vectors, one for each middle band. -/
def bandDifferenceGenerators : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun x := ![x 0, -x 0, x 1, -x 1]
  map_add' := by intros; ext i; fin_cases i <;> simp [add_comm]
  map_smul' := by intros; ext i; fin_cases i <;> simp

theorem bandDifferenceGenerators_in_kernel (x : Fin 2 → ℤ) :
    bandIncidence (bandDifferenceGenerators x) = 0 := by
  apply Prod.ext
  · simp [bandIncidence, bandDifferenceGenerators]
  · ext i; fin_cases i <;> simp [bandIncidence, bandDifferenceGenerators]

/-- The four-window incidence kernel has exactly the displayed two generators. -/
noncomputable def bandIncidenceKernelEquiv :
    (Fin 2 → ℤ) ≃ₗ[ℤ] LinearMap.ker bandIncidence where
  toFun x := ⟨bandDifferenceGenerators x, bandDifferenceGenerators_in_kernel x⟩
  invFun x := ![x.1 0, x.1 2]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by
    apply Subtype.ext
    have h0 := congrArg (fun y : ℤ × (Fin 2 → ℤ) => y.2 0) x.2
    have h1 := congrArg (fun y : ℤ × (Fin 2 → ℤ) => y.2 1) x.2
    simp [bandIncidence] at h0 h1
    ext i
    fin_cases i <;> simp [bandDifferenceGenerators] <;> omega
  map_add' := by intros; apply Subtype.ext; exact bandDifferenceGenerators.map_add _ _
  map_smul' := by intros; apply Subtype.ext; exact bandDifferenceGenerators.map_smul _ _

#print axioms bandIncidenceKernelEquiv
end CurveComplex.CapBandGeometry
