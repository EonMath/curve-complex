import CurveComplexGenusTwo.Dictionary.MarkedSphere

namespace CurveComplex
open Set Topology

variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem BranchedDoubleCover.actual_unramified_chart (q : BranchedDoubleCover E S)
    (x : E) (hx : x ∉ q.ramification) :
    ∃ e : OpenPartialHomeomorph E S, x ∈ e.source ∧
      (∀ y : E, e y = q.projection y) ∧
      ∀ y ∈ e.source, ∀ z ∈ e.source,
        q.projection y = q.projection z → y = z := by
  have hqx : q.projection x ∈ (q.branch : Set S)ᶜ := hx
  obtain ⟨e, he, heq⟩ := q.unbranched_cover.isLocalHomeomorphOn x hqx
  refine ⟨e, he, fun y => congrFun heq.symm y, ?_⟩
  intro y hy z hz h
  apply e.injOn hy hz
  rw [← congrFun heq y, ← congrFun heq z]
  exact h

theorem BranchedDoubleCover.actual_ramification_chart (q : BranchedDoubleCover E S)
    (x : E) (hx : x ∈ q.ramification) :
    ∃ c : SquareBranchChart E S q.projection x,
      x ∈ c.upstairs.source ∧ c.upstairs x = 0 ∧
      q.projection x ∈ c.downstairs.source ∧ c.downstairs (q.projection x) = 0 ∧
      ∀ y ∈ c.upstairs.source,
        c.downstairs (q.projection y) = (c.upstairs y)^2 := by
  let c := q.branch_chart x hx
  exact ⟨c, c.upstairs_mem, c.upstairs_center, c.downstairs_mem,
    c.downstairs_center, c.square⟩

end CurveComplex
