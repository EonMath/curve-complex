import CurveComplexGenusTwo.Dictionary.JordanEssentiality
import Mathlib.Topology.Order.Compact

namespace CurveComplex.HyperellipticModel
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
noncomputable section

/-- The ORIGINAL loop constructs an actual Schoenflies disk and a positive
boundary collar avoiding every mark except its literal common basepoint. -/
theorem actual_loop_marked_closed_disk_collar
    (M : HyperellipticModel E S) (a : EssentialMarkedArc M)
    (ha : a.val.map 0 = a.val.map 1) :
    ∃ U : Set S, ∃ D : ComplementaryDiscSide a.val U,
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧
      ∀ x : JordanClosedDisk, ρ ≤ ‖x.val‖ →
        (D.closedDisk x).val ∉ ((M.cover.branch : Set S) \ {a.val.map 0}) := by
  classical
  let : T2Space S := M.sphere.symm.t2Space
  obtain ⟨T⟩ := markedLoop_disc_decomposition_exists M a.val ha
  let U := T.side 0
  let D := T.discs 0
  let bad : Set JordanClosedDisk :=
    {x | (D.closedDisk x).val ∈ ((M.cover.branch : Set S) \ {a.val.map 0})}
  have hbclosed : IsClosed bad :=
    (M.cover.branch.finite_toSet.subset sdiff_subset).isClosed.preimage
      (continuous_subtype_val.comp D.closedDisk.continuous)
  have hbadnorm (x : JordanClosedDisk) (hx : x ∈ bad) : ‖x.val‖ < 1 := by
    have hle : ‖x.val‖ ≤ 1 := by simpa only [Metric.mem_closedBall,dist_zero_right] using x.property
    apply lt_of_le_of_ne hle
    intro he
    obtain ⟨t,ht⟩ := (D.disk_boundary x).mpr he
    have hm : a.val.map t ∈ M.cover.branch := ht ▸ hx.1
    rcases a.val.marked_only_at_ends t hm with h0 | h1
    · exact hx.2 (mem_singleton_iff.mpr (ht.symm.trans (congrArg a.val.map h0)))
    · exact hx.2 (mem_singleton_iff.mpr (ht.symm.trans ((congrArg a.val.map h1).trans ha.symm)))
  by_cases hb : bad.Nonempty
  · obtain ⟨x,hx,hmax⟩ := hbclosed.isCompact.exists_isMaxOn hb
      (continuous_norm.comp continuous_subtype_val).continuousOn
    let ρ := (‖x.val‖+1)/2
    have hρ : 0 < ρ := by dsimp [ρ]; positivity
    have hρ1 : ρ < 1 := by dsimp [ρ]; linarith [hbadnorm x hx]
    refine ⟨U,D,ρ,hρ,hρ1,?_⟩
    intro y hy hbad
    have hh : ‖y.val‖ ≤ ‖x.val‖ := hmax hbad
    dsimp [ρ] at hy
    linarith [hbadnorm x hx]
  · refine ⟨U,D,1/2,by norm_num,by norm_num,?_⟩
    intro x _ hx
    exact hb ⟨x,hx⟩
end
end CurveComplex.HyperellipticModel
