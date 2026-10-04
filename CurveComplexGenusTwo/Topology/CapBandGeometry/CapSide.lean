import CurveComplexGenusTwo.Foundations.Definitions
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Closure

open Set Topology

namespace CurveComplex

private abbrev Plane := EuclideanSpace ℝ (Fin 2)
private abbrev UnitDisk := Metric.closedBall (0 : Plane) 1
private def diskInterior : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.ball 0 1}
private def diskBoundary : Set UnitDisk :=
  {x | (x : Plane) ∈ Metric.sphere 0 1}

/-- A connected subset disjoint from a frontier lies entirely on one side. -/
theorem connected_cap_side {S : Type*} [TopologicalSpace S]
    (N D : Set S) (hD : IsPreconnected D)
    (havoid : Disjoint D (frontier N)) :
    D ⊆ interior N ∨ D ⊆ interior Nᶜ := by
  apply hD.subset_or_subset isOpen_interior isOpen_interior
    (Set.disjoint_left.mpr (by
      intro x hxN hxC
      exact (interior_subset hxC) (interior_subset hxN)))
  intro x hx
  have hx' : x ∈ (frontier N)ᶜ := by
    exact (Set.disjoint_left.mp havoid hx)
  exact (compl_frontier_eq_union_interior (s := N)) ▸ hx'

/-- The interior of an embedded disk does not meet its boundary image. -/
theorem embedded_disk_interior_disjoint_boundary {S : Type*} [TopologicalSpace S]
    (f : C(UnitDisk, S)) (hf : IsEmbedding f) :
    Disjoint (f '' diskInterior) (f '' diskBoundary) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨u, hu, rfl⟩ ⟨v, hv, heq⟩
  have huv : u = v := hf.injective heq.symm
  subst v
  exact (ne_of_lt hu) hv

/-- Side separation for the exact disk embedding supplied by a witness. -/
theorem embedded_disk_side_same_map {S : Type*} [TopologicalSpace S]
    (N : Set S) (c : Curve S) (hfront : frontier N = c.image)
    (f : C(UnitDisk, S)) (hf : IsEmbedding f)
    (hboundary : f '' diskBoundary = c.image) :
    f '' diskInterior ⊆ interior N ∨
      f '' diskInterior ⊆ interior Nᶜ := by
  apply connected_cap_side N (f '' diskInterior)
  · have hbi : IsPreconnected diskInterior := by
      apply IsInducing.subtypeVal.isPreconnected_image.mp
      have heq : (Subtype.val : UnitDisk → Plane) '' diskInterior =
          Metric.ball 0 1 := by
        ext x
        constructor
        · rintro ⟨y, hy, rfl⟩
          exact hy
        · intro hx
          exact ⟨⟨x, Metric.ball_subset_closedBall hx⟩, hx, rfl⟩
      rw [heq]
      exact (convex_ball (0 : Plane) 1).isPreconnected
    exact hbi.image f f.continuous.continuousOn
  · rw [hfront, ← hboundary]
    exact embedded_disk_interior_disjoint_boundary f hf

/-- The interior of a hypothetical bounding disk lies on one side of N. -/
theorem bounding_disk_side {S : Type*} [TopologicalSpace S]
    (N : Set S) (c : Curve S) (hfront : frontier N = c.image)
    (hbound : BoundsDisc c) :
    ∃ f : C(UnitDisk, S), IsEmbedding f ∧
      (f '' diskInterior ⊆ interior N ∨ f '' diskInterior ⊆ interior Nᶜ) := by
  obtain ⟨f, hf, hboundary⟩ := hbound
  exact ⟨f, hf, embedded_disk_side_same_map N c hfront f hf hboundary⟩

end CurveComplex

#print axioms CurveComplex.bounding_disk_side
