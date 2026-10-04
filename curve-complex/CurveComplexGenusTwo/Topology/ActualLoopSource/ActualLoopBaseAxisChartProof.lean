import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualLoopBaseExactStrip
import CurveComplexGenusTwo.Topology.ActualLoopSource.ActualExactStripPointChartAvoiding
namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
/-- Actual original-loop base chart; exact header of the bounded review scaffold. -/
theorem actual_loop_base_axis_chart
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0=a.val.map 1) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      Plane.closedSquare 0 1 ⊆ V ∧
      Disjoint U ((M.cover.branch : Set S) \ {a.val.map 0}) ∧
      (∀ q : U, q.val ∈ a.val.image ↔ (e q).val 1=0) ∧
      ∃ hp : a.val.map 0 ∈ U, (e ⟨a.val.map 0,hp⟩).val=0 := by
  obtain ⟨B,hB,hmid,hmarks,haxis⟩ := actual_loop_base_exact_strip M a ha
  obtain ⟨U,V,hU,e,hCV,hm,ha',hp,hp0⟩ := actual_exact_strip_point_chart_avoiding
    M a.val.image ((M.cover.branch : Set S) \ {a.val.map 0}) B hB hmarks haxis
  have hp' : a.val.map 0 ∈ U := hmid ▸ hp
  refine ⟨U,V,hU,e,hCV,hm,ha',hp',?_⟩
  have he : (⟨a.val.map 0,hp'⟩ : U)=⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hp⟩ :=
    Subtype.ext hmid.symm
  rw [he]
  exact hp0
end CurveComplex.HyperellipticModel.ArcSurgery
