import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts

namespace CurveComplex
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S] [T1Space S]

theorem BranchedDoubleCover.actual_branch_deck_coordinate_neighborhood
    (q : BranchedDoubleCover E S) (x : E) (hx : x ∈ q.ramification) :
    ∃ c : SquareBranchChart E S q.projection x, ∃ U : Set E,
      IsOpen U ∧ x ∈ U ∧ U ⊆ c.upstairs.source ∧
      (∀ y ∈ U, q.deck y ∈ U) ∧
      (∀ y ∈ U, y ∈ q.ramification ↔ y = x) ∧
      ∀ y ∈ U, c.upstairs (q.deck y) = -c.upstairs y := by
  classical
  let c := q.branch_chart x hx
  let B : Set S := (q.branch : Set S) \ {q.projection x}
  have hB : IsClosed B := q.branch.finite_toSet.diff.isClosed
  let U : Set E := c.upstairs.source ∩ q.deck ⁻¹' c.upstairs.source ∩
    q.projection ⁻¹' Bᶜ
  have hU : IsOpen U := (c.upstairs.open_source.inter
    (c.upstairs.open_source.preimage q.deck.continuous)).inter
    (hB.isOpen_compl.preimage q.projection_continuous)
  have hdx : q.deck x = x := (q.fixed_iff_branch x).mpr hx
  have hxu : x ∈ U := by
    refine ⟨⟨c.upstairs_mem, ?_⟩, ?_⟩
    · change q.deck x ∈ c.upstairs.source
      rw [hdx]
      exact c.upstairs_mem
    · simp [B]
  have hstable : ∀ y ∈ U, q.deck y ∈ U := by
    intro y hy
    refine ⟨⟨hy.1.2, ?_⟩, ?_⟩
    · change q.deck (q.deck y) ∈ c.upstairs.source
      rw [q.deck_involution]
      exact hy.1.1
    · change q.projection (q.deck y) ∉ B
      rw [q.projection_deck]
      exact hy.2
  have hram : ∀ y ∈ U, y ∈ q.ramification ↔ y = x := by
    intro y hy
    constructor
    · intro hby
      have hproj : q.projection y = q.projection x := by
        by_contra hne
        exact hy.2 ⟨hby, hne⟩
      have hs := c.square y hy.1.1
      rw [hproj, c.downstairs_center] at hs
      have hzero : c.upstairs y = 0 := by
        exact (sq_eq_zero_iff).mp hs.symm
      apply c.upstairs.injOn hy.1.1 c.upstairs_mem
      rw [hzero, c.upstairs_center]
    · rintro rfl
      exact hx
  refine ⟨c, U, hU, hxu, fun y hy => hy.1.1, hstable, hram, ?_⟩
  intro y hy
  have hdy := (hstable y hy).1.1
  have hs : (c.upstairs (q.deck y)) ^ 2 = (c.upstairs y) ^ 2 := by
    rw [← c.square (q.deck y) hdy, ← c.square y hy.1.1, q.projection_deck]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with heq | heq
  · have hfixed : q.deck y = y := c.upstairs.injOn hdy hy.1.1 heq
    have hyx := (hram y hy).mp ((q.fixed_iff_branch y).mp hfixed)
    subst y
    rw [hdx, c.upstairs_center, neg_zero]
  · exact heq

end CurveComplex
