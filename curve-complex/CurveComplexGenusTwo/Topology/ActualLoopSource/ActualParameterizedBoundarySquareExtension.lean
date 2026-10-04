import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualParameterizedSquareConvexConeFilling
namespace CurveComplex.HyperellipticModel
open Set Topology
/-- The actual joint boundary movie has a constructed joint parameter-square
extension in the convex strip carrier, fixing every supplied boundary value. -/
theorem actual_parameterized_boundary_square_extension
    (V : Set (ℝ × ℝ)) (hV : Convex ℝ V)
    (f : C(Interval × {z : ℝ × ℝ // ‖z‖=1},V)) (v : C(Interval,V)) :
    ∃ H : C((Interval × Interval) × Interval,V),
      ∀ σ (z : {z : ℝ × ℝ // ‖z‖=1}),
        H (actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩,σ)=f (σ,z) := by
  obtain ⟨G,hboundary,hformula⟩ := actual_parameterized_square_convex_cone_filling V hV f v
  let H : C((Interval × Interval) × Interval,V) :=
    ⟨fun z => G (z.2,actualNormalizedMaxNormSquare.symm z.1),by fun_prop⟩
  refine ⟨H,?_⟩
  intro σ z
  change G (σ,actualNormalizedMaxNormSquare.symm
    (actualNormalizedMaxNormSquare ⟨z.val,z.property.le⟩))=f (σ,z)
  rw [actualNormalizedMaxNormSquare.symm_apply_apply,hboundary]
end CurveComplex.HyperellipticModel
