import CurveComplexGenusTwo.Filtration.StarSmallHomology

open CategoryTheory
open scoped Simplicial
set_option backward.isDefEq.respectTransparency false
namespace CurveGenusTwo.Filtration
variable {V : Type} [LinearOrder V]

/-- The positive comparison surjectivity problem is exactly the remaining
comparison problem for cycles of the actual star-small subcomplex. -/
theorem singularPositiveCycle_lift_iff_starSmall (K : FiniteComplex V) (n : ℕ) :
    (∀ z : singularPositiveCycles K n,
      ∃ c : cycles K ((n + 1 : ℕ) : ℤ),
        z.1 - (positiveCyclesMap K n c).1 ∈ singularPositiveBoundaries K n) ↔
    (∀ a : FreeAbelianGroup (StarSmallSimplex K (n+1)),
      starSmallBoundary K n a = 0 →
      ∃ c : cycles K ((n + 1 : ℕ) : ℤ),
        starSmallChainInclusion K (n+1) a - (positiveCyclesMap K n c).1 ∈
          singularPositiveBoundaries K n) := by
  constructor
  · intro h a ha
    have hz : starSmallChainInclusion K (n+1) a ∈ singularPositiveCycles K n := by
      change singularGeneratorBoundary K n _ = 0
      rw [← starSmallChainInclusion_boundary, ha, map_zero]
    exact h ⟨_, hz⟩
  · intro h z
    obtain ⟨a, ha, haz⟩ := singularPositiveCycle_has_smallComplex_representative K n z
    obtain ⟨c, hc⟩ := h a ha
    refine ⟨c, ?_⟩
    have hh := (singularPositiveBoundaries K n).sub_mem hc haz
    convert hh using 1 <;> abel

#print axioms singularPositiveCycle_lift_iff_starSmall
end CurveGenusTwo.Filtration
