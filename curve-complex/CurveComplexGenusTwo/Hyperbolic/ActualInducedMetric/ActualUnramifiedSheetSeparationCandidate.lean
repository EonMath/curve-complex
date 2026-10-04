import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts

namespace CurveComplex
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem actual_unramified_two_sheet_neighborhood (q : BranchedDoubleCover E S) (x : E) (hx : x ∉ q.ramification) :
    ∃ V : Set S, IsOpen V ∧ q.projection x ∈ V ∧ V ⊆ (q.branch : Set S)ᶜ ∧
      ∃ A : Set E, IsOpen A ∧ x ∈ A ∧
        A ⊆ q.projection ⁻¹' V ∧
        (∀ y : E, q.projection y ∈ V → y ∈ A ∨ q.deck y ∈ A) ∧
        (∀ y ∈ A, q.deck y ∉ A) := by
  obtain ⟨u, hux, huq, huinj⟩ := q.actual_unramified_chart x hx
  let V := u.target ∩ (q.branch : Set S)ᶜ
  have hV : IsOpen V := u.open_target.inter q.branch.finite_toSet.isClosed.isOpen_compl
  have hxV : q.projection x ∈ V :=
    ⟨by rw [← huq x]; exact u.map_source hux, hx⟩
  let A := u.source ∩ q.projection ⁻¹' V
  have hA : IsOpen A := u.open_source.inter (hV.preimage q.projection_continuous)
  refine ⟨V, hV, hxV, Set.inter_subset_right, A, hA, ⟨hux, hxV⟩,
    Set.inter_subset_right, ?_, ?_⟩
  · intro y hy
    let z := u.symm (q.projection y)
    have hzs : z ∈ u.source := u.map_target hy.1
    have hzy : q.projection z = q.projection y := by
      rw [← huq z]
      exact u.right_inv hy.1
    have hzA : z ∈ A := ⟨hzs, by simpa only [Set.mem_preimage, hzy] using hy⟩
    rcases (q.fiber_pair z y).mp hzy with heq | heq
    · exact Or.inl (heq.symm ▸ hzA)
    · apply Or.inr
      rw [heq, q.deck_involution]
      exact hzA
  · intro y hy hdy
    have hfixed : q.deck y = y :=
      huinj _ hdy.1 _ hy.1 (q.projection_deck y)
    have hram := (q.fixed_iff_branch y).mp hfixed
    exact hy.2.2 hram

end CurveComplex
