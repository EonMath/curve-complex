import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualPeriodDualCanonical85
import Mathlib.Algebra.Module.LinearMap.Star

open scoped Manifold ContDiff Bundle Simplicial TensorProduct
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

noncomputable def actualConjugatePeriodOnProject {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) :
    CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ where
  toFun x := star (actualSectionPeriodOnProject s x)
  map_add' x y := by simp
  map_smul' n x := by
    simp

theorem actualConjugatePeriodToDual_tmul {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (c : ℂ)
    (x : CurveComplex.integralHomology E 1) :
    (actualPeriodToDual E (actualConjugatePeriodOnProject s))
      (c ⊗ₜ[ℤ] x) =
      c * star (actualSectionPeriodOnProject s x) := by
  change (TensorProduct.AlgebraTensorModule.lift
      ((LinearMap.lsmul ℂ
        (CurveComplex.integralHomology E 1 →ₗ[ℤ] ℂ)).flip
        (actualConjugatePeriodOnProject s))) (c ⊗ₜ[ℤ] x) = _
  rw [TensorProduct.AlgebraTensorModule.lift_tmul]
  change (c • actualConjugatePeriodOnProject s) x = _
  simp [actualConjugatePeriodOnProject, smul_eq_mul]

noncomputable def actualConjugatePeriodDual {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E] :
    ActualCanonicalSection E →ₗ⋆[ℂ]
      Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) where
  toFun s := actualPeriodToDual E (actualConjugatePeriodOnProject s)
  map_add' s t := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      rw [actualConjugatePeriodToDual_tmul,
        LinearMap.add_apply, actualConjugatePeriodToDual_tmul,
        actualConjugatePeriodToDual_tmul]
      change c * star (actualSectionPeriodOnProjectLinear (s + t) y) = _
      rw [map_add]
      simp [actualSectionPeriodOnProjectLinear, star_add, mul_add]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  map_smul' c s := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul d y =>
      rw [actualConjugatePeriodToDual_tmul,
        LinearMap.smul_apply, actualConjugatePeriodToDual_tmul]
      change d * star (actualSectionPeriodOnProjectLinear (c • s) y) = _
      rw [map_smul]
      simp [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm,
        actualSectionPeriodOnProjectLinear]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem actualConjugatePeriodDual_tmul {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s : ActualCanonicalSection E) (c : ℂ)
    (x : CurveComplex.integralHomology E 1) :
    (actualConjugatePeriodDual s) (c ⊗ₜ[ℤ] x) =
      c * star (actualSectionPeriodOnProject s x) := by
  exact actualConjugatePeriodToDual_tmul s c x

end CanonicalDimensionTwo
