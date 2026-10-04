import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualMaxNormSquareBoundaryFaceCollision
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- Every literal closed mesh subinterval is covered by its affine parameter. -/
theorem actual_mesh_interval_parameter_cover (x y t : Interval)
    (ht : t ∈ Icc x y) : ∃ s : Interval,Icc.convexComb x y s=t := by
  have hval : t ∈ Icc (Icc.convexComb x y 0) (Icc.convexComb x y 1) := by
    simpa only [Icc.convexComb_zero,Icc.convexComb_one] using ht
  obtain ⟨s,hs,he⟩ := intermediate_value_Icc (show (0:Interval)≤1 by norm_num)
    (Icc.continuous_convexComb x y).continuousOn hval
  exact ⟨s,he⟩
end CurveComplex.HyperellipticModel
