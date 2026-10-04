import CurveComplexGenusTwo.Topology.ActualCanonicalDimensionTwo.ActualHodgePeriodCanonical85

open scoped Manifold ContDiff Bundle Simplicial TensorProduct
open CanonicalDimensionTwo

namespace CanonicalDimensionTwo

theorem actualHodgePeriod_zero_iff_regular_cycle {E : Type}
    [TopologicalSpace E] [ChartedSpace ℂ E] [IsManifold 𝓘(ℂ) ∞ E]
    (s t : ActualCanonicalSection E) :
    actualHodgePeriod (s, t) = 0 ↔
      ∀ z : ActualRegularOneCycles E,
        actualRegularCyclePeriod s z +
          star (actualRegularCyclePeriod t z) = 0 := by
  constructor
  · intro h z
    have hval := congrArg
      (fun f : Module.Dual ℂ (ℂ ⊗[ℤ] CurveComplex.integralHomology E 1) =>
        f (1 ⊗ₜ[ℤ] (intervalLocalNormalizedRegularHOneToProject
          ((intervalLocalNormalizedRelations (E := E)).mkQ z)))) h
    rw [actualHodgePeriod_apply, one_mul,
      actualSectionPeriodOnProject_mk,
      actualSectionPeriodOnProject_mk] at hval
    simpa using hval
  · intro h
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c y =>
      obtain ⟨q, rfl⟩ :=
        intervalLocalNormalizedRegularHOneToProject_surjective y
      obtain ⟨z, rfl⟩ :=
        (intervalLocalNormalizedRelations (E := E)).mkQ_surjective q
      rw [actualHodgePeriod_apply,
        actualSectionPeriodOnProject_mk,
        actualSectionPeriodOnProject_mk,
        h z, mul_zero]
      simp
    | add x y hx hy =>
      simpa only [map_add, add_zero] using congrArg₂ (· + ·) hx hy

end CanonicalDimensionTwo
