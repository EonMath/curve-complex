import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualUniformZeroGermSmallness
namespace CurveComplex.HyperellipticModel
open Set Topology Schoenflies
/-- The actual jointly continuous plane germ yields a single literal square
window along its whole time axis. -/
theorem actual_small_plane_zero_germ_square
    (D : C(unitInterval × unitInterval,Plane)) (hD : ∀ τ,D (τ,0)=0) :
    ∃ δ : ℝ, 0<δ ∧ δ<1/2 ∧ ∀ τ t : unitInterval,
      (t:ℝ)≤δ → D (τ,t) ∈ Plane.closedSquare 0 1 := by
  let g : C(unitInterval × unitInterval,ℂ) :=
    ⟨fun z => ArcFinitePosition.planeComplexLinearEquiv (D z),by fun_prop⟩
  have hg (τ : unitInterval) : g (τ,0)=0 := by
    change ArcFinitePosition.planeComplexLinearEquiv (D (τ,0))=0
    rw [hD]; exact map_zero _
  obtain ⟨δ,hδ,hhalf,hbound⟩ := actual_uniform_zero_germ_smallness g hg 1 (by norm_num)
  refine ⟨δ,hδ,hhalf,?_⟩
  intro τ t ht
  have hh := actual_complex_unit_ball_plane_square (g (τ,t)) (hbound τ t ht).le
  simpa only [g,ContinuousMap.coe_mk,ContinuousLinearEquiv.symm_apply_apply] using hh
end CurveComplex.HyperellipticModel
