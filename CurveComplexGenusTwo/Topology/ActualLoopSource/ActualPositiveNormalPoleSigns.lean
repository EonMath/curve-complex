import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualAffineNormalRootSigns
namespace CurveComplex.HyperellipticModel
/-- The actual selected-cell pole has positive normal coordinate one-half;
normalizing by it preserves literal source signs and nonvanishing. -/
theorem actual_positive_normal_pole_signs (x y : ℝ)
    (hx : x≠0) (hy : y≠0) (hflip : (0<x) ↔ ¬(0<y)) :
    x/(1/2:ℝ)≠0 ∧ y/(1/2:ℝ)≠0 ∧
      ((0<x/(1/2:ℝ)) ↔ ¬(0<y/(1/2:ℝ))) := by
  have hp : (0:ℝ)<1/2 := by norm_num
  exact ⟨div_ne_zero hx hp.ne',div_ne_zero hy hp.ne',by
    simpa only [div_pos_iff_of_pos_right hp] using hflip⟩
end CurveComplex.HyperellipticModel
