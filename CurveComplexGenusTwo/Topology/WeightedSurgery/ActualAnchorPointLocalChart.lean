import CurveComplexGenusTwo.Topology.WeightedSurgery.ActualEmbeddedAnchorPointChart

namespace CurveComplex.HyperellipticModel.ArcSurgery
open Set Topology Schoenflies CurveComplex.ActualCrossingSlide
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- Every literal interior point of the actual stationary anchor has an exact
whole-anchor axis chart, including loop anchors. It is constructed from the
anchor alone, without a transverse moving representative or a bank atlas. -/
theorem actual_anchor_parameter_axis_chart
    (M : HyperellipticModel E S) (anchor : EssentialMarkedArc M)
    (r : Interval) (hr : 0 < r.val ∧ r.val < 1) :
    ∃ U : Set S, ∃ V : Set Plane, ∃ _hU : IsOpen U, ∃ e : U ≃ₜ V,
      Plane.closedSquare 0 1 ⊆ V ∧ Disjoint U (M.cover.branch : Set S) ∧
      (∀ q : U, q.val ∈ anchor.val.image ↔ (e q).val 1 = 0) ∧
      ∃ hp : anchor.val.map r ∈ U, (e ⟨anchor.val.map r,hp⟩).val = 0 := by
  let δ := min r.val (1-r.val) / 2
  have hδ : 0 < δ := half_pos (lt_min hr.1 (by linarith [hr.2]))
  have hδr : δ ≤ r.val/2 := by dsimp [δ]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hδ1 : δ ≤ (1-r.val)/2 := by dsimp [δ]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  let α := r.val-δ
  let β := r.val+δ
  have hα : 0 < α := by dsimp [α]; linarith
  have hβ : β < 1 := by dsimp [β]; linarith
  have hαβ : α < β := by dsimp [α,β]; linarith
  obtain ⟨B,hB,hcenter,hmarks,haxis⟩ := actual_anchor_interior_core_exact_strip M anchor
    α β hα hβ hαβ
  have hmid : B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩) = anchor.val.map r := by
    rw [hcenter]
    apply congrArg anchor.val.map
    apply Subtype.ext
    dsimp [actualCoreParameter,α,β]
    ring
  obtain ⟨U,V,hU,e,hCV,hm,ha,hp,hp0⟩ := actual_exact_anchor_strip_point_chart M anchor B hB hmarks haxis
  have hp' : anchor.val.map r ∈ U := hmid ▸ hp
  refine ⟨U,V,hU,e,hCV,hm,ha,hp',?_⟩
  have he : (⟨anchor.val.map r,hp'⟩ : U) = ⟨B (⟨1/2,by norm_num⟩,⟨0,by norm_num⟩),hp⟩ :=
    Subtype.ext hmid.symm
  rw [he]
  exact hp0
end
end CurveComplex.HyperellipticModel.ArcSurgery
