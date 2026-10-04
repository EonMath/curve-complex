import CurveComplexGenusTwo.Dictionary.Genus
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dimension.Finite

open scoped TensorProduct

namespace CanonicalDimensionTwo

theorem genus_two_integral_h1_four
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) :
    Nonempty (CurveComplex.integralHomology E 1 ≅
      ModuleCat.of ℤ (Fin 4 → ℤ)) := by
  rcases hg with ⟨_, _, _, h₁⟩
  simpa using h₁

noncomputable def genus_two_complexified_h1_basis
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) :
    Module.Basis (Fin 4) ℂ
      (ℂ ⊗[ℤ] (CurveComplex.integralHomology E 1)) := by
  let e := Classical.choice (genus_two_integral_h1_four E hg)
  let b : Module.Basis (Fin 4) ℤ (CurveComplex.integralHomology E 1) :=
    (Pi.basisFun ℤ (Fin 4)).map e.symm.toLinearEquiv
  exact b.baseChange ℂ

noncomputable def genus_two_complex_h1_dual_basis
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) :
    Module.Basis (Fin 4) ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] (CurveComplex.integralHomology E 1))) :=
  (genus_two_complexified_h1_basis E hg).dualBasis

theorem genus_two_complex_h1_dual_finrank_four
    (E : Type) [TopologicalSpace E]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
    (hg : CurveComplex.IsGenus E 2) :
    Module.finrank ℂ
      (Module.Dual ℂ (ℂ ⊗[ℤ] (CurveComplex.integralHomology E 1))) = 4 := by
  rw [Module.finrank_eq_card_basis (genus_two_complex_h1_dual_basis E hg)]
  simp

end CanonicalDimensionTwo
