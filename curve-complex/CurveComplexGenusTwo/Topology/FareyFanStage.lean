import CurveComplexGenusTwo.Topology.FareyGlobalFiltration
import CurveComplexGenusTwo.Topology.FareyFan

set_option maxHeartbeats 1000000

namespace CurveComplexGenusTwo.Topology

open CurveComplex

/-- The denominator-one vertices are exactly infinity and the integral
slopes, which form the fan contracted by `fareyFan_contractible`. -/
theorem fareyDenominator_one_iff_fan (v : FareySlope) :
    fareyDenominator v ≤ 1 ↔ ∃ i : Option ℤ, fareyFanSlope i = v := by
  constructor
  · intro hv
    cases v with
    | none => exact ⟨none, rfl⟩
    | some q =>
        have hden : q.den = 1 := by
          have hpos := q.den_pos
          change q.den ≤ 1 at hv
          omega
        refine ⟨some q.num, ?_⟩
        simp only [fareyFanSlope, Option.some.injEq]
        conv_rhs => rw [← Rat.num_div_den q]
        rw [hden]
        norm_num
  · rintro ⟨i, rfl⟩
    cases i with
    | none => simp [fareyFanSlope, fareyDenominator]
    | some n => simp [fareyFanSlope, fareyDenominator]

theorem fareyFanSlope_injective : Function.Injective fareyFanSlope := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some n => simp [fareyFanSlope] at hij
  | some m =>
      cases j with
      | none => simp [fareyFanSlope] at hij
      | some n =>
          simp only [fareyFanSlope, Option.some.injEq] at hij
          exact congrArg some (Int.cast_injective hij)

end CurveComplexGenusTwo.Topology
