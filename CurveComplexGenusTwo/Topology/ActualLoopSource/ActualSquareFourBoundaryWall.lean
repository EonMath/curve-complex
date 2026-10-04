import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualPreparedLoopFiniteCoreSupport
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Constructed scalar wall for the actual prepared square: zero on EVERY
literal boundary side, strictly positive throughout the interior, and bounded
by one. It makes supported normal shifts genuinely boundary-relative. -/
theorem actual_square_four_boundary_wall :
    ∃ wall : C(Interval × Interval,ℝ),
      (∀ z,wall z=z.1.val*(1-z.1.val)*z.2.val*(1-z.2.val)) ∧
      (∀ z,wall z ∈ Icc (0:ℝ) 1) ∧
      (∀ z,z.1=0 ∨ z.1=1 ∨ z.2=0 ∨ z.2=1 → wall z=0) ∧
      (∀ z,0<z.1.val → z.1.val<1 → 0<z.2.val → z.2.val<1 → 0<wall z) := by
  let wall : C(Interval × Interval,ℝ) :=
    ⟨fun z => z.1.val*(1-z.1.val)*z.2.val*(1-z.2.val),by fun_prop⟩
  refine ⟨wall,(fun _ => rfl),?_,?_,?_⟩
  · intro z
    have ha0 := z.1.property.1
    have ha1 := z.1.property.2
    have hb0 := z.2.property.1
    have hb1 := z.2.property.2
    have hac : 0≤1-z.1.val := sub_nonneg.mpr ha1
    have hbc : 0≤1-z.2.val := sub_nonneg.mpr hb1
    have hprod0 : 0≤z.1.val*(1-z.1.val) := mul_nonneg ha0 hac
    have hprod1 : z.1.val*(1-z.1.val)≤1 := by
      have hm := mul_nonneg ha0 ha0
      nlinarith only [ha0,ha1,hm]
    have hprod2 : 0≤z.1.val*(1-z.1.val)*z.2.val := mul_nonneg hprod0 hb0
    have hprod3 : z.1.val*(1-z.1.val)*z.2.val≤1 :=
      (mul_le_mul_of_nonneg_right hprod1 hb0).trans (by simpa using hb1)
    constructor
    · exact mul_nonneg hprod2 hbc
    · have hm := mul_le_mul_of_nonneg_left (by linarith only [hb0] : 1-z.2.val≤1) hprod2
      exact hm.trans (by simpa only [mul_one] using hprod3)
  · intro z hz
    rcases hz with h | h | h | h
    all_goals simp [wall,h]
  · intro z ha0 ha1 hb0 hb1
    change 0<z.1.val*(1-z.1.val)*z.2.val*(1-z.2.val)
    exact mul_pos (mul_pos (mul_pos ha0 (sub_pos.mpr ha1)) hb0) (sub_pos.mpr hb1)
end CurveComplex.HyperellipticModel
