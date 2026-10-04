import CurveComplexGenusTwo.Hyperbolic.ActualInducedMetric.ActualCoverLocalCharts

namespace CurveComplex
open Set Topology
variable {E S : Type} [TopologicalSpace E] [TopologicalSpace S]

theorem BranchedDoubleCover.actual_branch_fiber_singleton
    (q : BranchedDoubleCover E S) (x : E) (hx : x ∈ q.ramification) :
    q.projection ⁻¹' {q.projection x} = {x} := by
  have hfixed := (q.fixed_iff_branch x).mpr hx
  ext y
  change q.projection y = q.projection x ↔ y = x
  constructor
  · intro hy
    rcases (q.fiber_pair x y).mp hy.symm with hy | hy
    · exact hy
    · exact hy.trans hfixed
  · rintro rfl
    rfl

theorem BranchedDoubleCover.actual_branch_neighborhood_control
    [CompactSpace E] [T2Space S] (q : BranchedDoubleCover E S)
    (x : E) (hx : x ∈ q.ramification) (U : Set E) (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ V : Set S, IsOpen V ∧ q.projection x ∈ V ∧ q.projection ⁻¹' V ⊆ U := by
  let V := (q.projection '' Uᶜ)ᶜ
  have hclosed : IsClosed (q.projection '' Uᶜ) :=
    q.projection_continuous.isClosedMap _ hU.isClosed_compl
  refine ⟨V, hclosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨y, hy, hproj⟩
    have hys : y ∈ q.projection ⁻¹' {q.projection x} := hproj
    rw [q.actual_branch_fiber_singleton x hx] at hys
    have hyx : y = x := hys
    subst y
    exact hy hxU
  · intro y hy
    by_contra hyU
    exact hy ⟨y, hyU, rfl⟩

theorem BranchedDoubleCover.actual_branch_lift_continuousAt
    [CompactSpace E] [T2Space S] {A : Type} [TopologicalSpace A]
    (q : BranchedDoubleCover E S) (g : A → E) (a : A)
    (ha : g a ∈ q.ramification)
    (hprojection : ContinuousAt (fun b => q.projection (g b)) a) :
    ContinuousAt g a := by
  rw [continuousAt_def]
  intro B hB
  obtain ⟨U, hUB, hU, haU⟩ := mem_nhds_iff.mp hB
  obtain ⟨V, hV, haV, hVU⟩ := q.actual_branch_neighborhood_control (g a) ha U hU haU
  have hpre := continuousAt_def.mp hprojection V (hV.mem_nhds haV)
  exact Filter.mem_of_superset hpre (fun b hb => hUB (hVU hb))

end CurveComplex
