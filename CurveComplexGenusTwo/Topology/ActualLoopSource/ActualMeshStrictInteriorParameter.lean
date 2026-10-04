import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualSquareConeFiniteWholeContactFamily
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Interior parameters remain strict interior of their actual mesh interval. -/
theorem actual_mesh_strict_interior_parameter (x y t : Interval) (hxy : x<y)
    (ht0 : 0<t.val) (ht1 : t.val<1) :
    x<Icc.convexComb x y t ∧ Icc.convexComb x y t<y := by
  change x.val<(1-t.val)*x.val+t.val*y.val ∧ (1-t.val)*x.val+t.val*y.val<y.val
  have hs : (x:ℝ)<y := hxy
  constructor
  · have hp := mul_pos ht0 (sub_pos.mpr hs)
    nlinarith only [hp]
  · have hp := mul_pos (sub_pos.mpr ht1) (sub_pos.mpr hs)
    nlinarith only [hp]
/-- A mesh parameter attaining the ambient square boundary must itself be an
endpoint. This is the actual endpoint control for radial face arc collisions. -/
theorem actual_mesh_parameter_boundary_endpoint (x y t : Interval) (hxy : x<y)
    (he : Icc.convexComb x y t=0 ∨ Icc.convexComb x y t=1) :
    t=0 ∨ t=1 := by
  by_cases h0 : t=0
  · exact Or.inl h0
  by_cases h1 : t=1
  · exact Or.inr h1
  have ht0 : 0<t.val := lt_of_le_of_ne t.property.1 (fun he => h0 (Subtype.ext he.symm))
  have ht1 : t.val<1 := lt_of_le_of_ne t.property.2 (fun he => h1 (Subtype.ext he))
  have hs := actual_mesh_strict_interior_parameter x y t hxy ht0 ht1
  rcases he with he | he
  · rw [he] at hs
    exact False.elim (not_lt_of_ge x.property.1 hs.1)
  · rw [he] at hs
    exact False.elim (not_lt_of_ge y.property.2 hs.2)
end CurveComplex.HyperellipticModel
