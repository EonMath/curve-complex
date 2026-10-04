import Mathlib

noncomputable section

namespace CurveComplex.Octagon.GraphMV

abbrev OverlapCoordinates := Fin 4 × Bool → ℤ
abbrev CoverCoordinates := ℤ × (Fin 4 → ℤ)

/-- The degree-zero MV difference in the component coordinates: every overlap
component maps to the vertex component and its corresponding edge component. -/
def difference : OverlapCoordinates →ₗ[ℤ] CoverCoordinates where
  toFun c := (∑ i : Fin 4, (c (i, false) + c (i, true)),
    fun i => c (i, false) + c (i, true))
  map_add' c d := by
    apply Prod.ext
    · change (∑ i : Fin 4, ((c (i, false) + d (i, false)) +
          (c (i, true) + d (i, true)))) =
        (∑ i : Fin 4, (c (i, false) + c (i, true))) +
          (∑ i : Fin 4, (d (i, false) + d (i, true)))
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      abel
    · funext i
      change (c (i, false) + d (i, false)) + (c (i, true) + d (i, true)) =
        (c (i, false) + c (i, true)) + (d (i, false) + d (i, true))
      abel
  map_smul' r c := by
    apply Prod.ext
    · change (∑ i : Fin 4, (r * c (i, false) + r * c (i, true))) =
        r * (∑ i : Fin 4, (c (i, false) + c (i, true)))
      simp_rw [← mul_add]
      calc
        (∑ i : Fin 4, r * (c (i, false) + c (i, true))) =
            ∑ i : Fin 4, r • (c (i, false) + c (i, true)) := by simp
        _ = r • (∑ i : Fin 4, (c (i, false) + c (i, true))) := Finset.smul_sum.symm
        _ = r * (∑ i : Fin 4, (c (i, false) + c (i, true))) := by simp
    · funext i
      change r * c (i, false) + r * c (i, true) =
        r * (c (i, false) + c (i, true))
      ring

/-- Read the starting-end coefficient of each of the four edges. -/
def kernelRead : LinearMap.ker difference →ₗ[ℤ] (Fin 4 → ℤ) where
  toFun c := fun i => c.1 (i, false)
  map_add' c d := by
    funext i
    rfl
  map_smul' r c := by
    funext i
    rfl

theorem kernel_end_eq_neg (c : LinearMap.ker difference) (i : Fin 4) :
    c.1 (i, true) = -c.1 (i, false) := by
  have h := congrArg (fun p : CoverCoordinates => p.2 i) c.2
  change c.1 (i, false) + c.1 (i, true) = 0 at h
  exact eq_neg_of_add_eq_zero_right h

/-- The MV kernel is free of rank four, with one starting-end coefficient per edge. -/
def kernelEquiv : LinearMap.ker difference ≃ₗ[ℤ] (Fin 4 → ℤ) :=
  LinearEquiv.ofBijective kernelRead (by
    constructor
    · intro c d h
      apply Subtype.ext
      funext p
      rcases p with ⟨i, b⟩
      cases b
      · exact congrFun h i
      · rw [kernel_end_eq_neg c i, kernel_end_eq_neg d i]
        exact congrArg Neg.neg (congrFun h i)
    · intro f
      let c : OverlapCoordinates := fun p => if p.2 then -f p.1 else f p.1
      have hc : difference c = 0 := by
        apply Prod.ext
        · change (∑ i : Fin 4, (c (i, false) + c (i, true))) = 0
          simp [c]
        · funext i
          change c (i, false) + c (i, true) = 0
          simp [c]
      exact ⟨⟨c, hc⟩, by funext i; rfl⟩)

end CurveComplex.Octagon.GraphMV

#print axioms CurveComplex.Octagon.GraphMV.kernelEquiv
