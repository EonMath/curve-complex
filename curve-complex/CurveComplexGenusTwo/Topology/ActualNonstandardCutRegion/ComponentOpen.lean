import CurveComplexGenusTwo.Filtration.Geometry.ComponentGeometry
import CurveComplexGenusTwo.Topology.OriginalBoundaryArc.ActualBoundaryProperArcStrip

open CurveComplex Set Topology

namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private abbrev arcTrace {S : Type} [TopologicalSpace S]
    {Q : Set S} {n : ℕ} (a : Fin n → C(Interval, ↥Q)) : Set S :=
  ⋃ i, Set.range (fun t => (a i t).val)

theorem finite_arcTrace_closed
    {S : Type} [TopologicalSpace S] [T2Space S]
    {Q : Set S} {n : ℕ} (a : Fin n → C(Interval, ↥Q)) :
    IsClosed (arcTrace a) := by
  apply isClosed_iUnion_of_finite
  intro i
  exact (isCompact_range (continuous_subtype_val.comp (a i).continuous)).isClosed

theorem original_disk_union_boundary_closed
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hS : IsGenus S g)
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target) :
    IsClosed (OriginalBoundaryArc.openDisk S x R ∪
      OriginalBoundaryArc.boundaryCircle S x R) := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  have hcompact : IsCompact
      ((chartAt Plane x).symm '' Metric.closedBall ((chartAt Plane x) x) R) :=
    (isCompact_closedBall _ _).image_of_continuousOn
      ((chartAt Plane x).continuousOn_symm.mono htarget)
  have hpartition :
      OriginalBoundaryArc.openDisk S x R ∪
        OriginalBoundaryArc.boundaryCircle S x R =
      (chartAt Plane x).symm '' Metric.closedBall ((chartAt Plane x) x) R := by
    dsimp [OriginalBoundaryArc.openDisk, OriginalBoundaryArc.boundaryCircle]
    rw [← Set.image_union]
    congr 1
    exact Metric.ball_union_sphere
  rw [hpartition]
  exact hcompact.isClosed

theorem original_cut_component_open_of_closed_base
    {S : Type} [TopologicalSpace S] [ChartedSpace Plane S]
    [T2Space S] {Q D B : Set S} {n : ℕ}
    (a : Fin n → C(Interval, ↥Q))
    (hbase : IsClosed (D ∪ B)) {U : Set S}
    (hU : CurveComplex.HyperellipticModel.IsComplementComponent
      (D ∪ B ∪ arcTrace a) U) : IsOpen U := by
  letI : LocallyConnectedSpace S := ChartedSpace.locallyConnectedSpace Plane S
  exact CurveComplex.HyperellipticModel.complementComponent_open
    (hbase.union (finite_arcTrace_closed a)) hU

theorem original_cut_component_open
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hS : IsGenus S g)
    (x : S) (R : ℝ)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (n : ℕ)
    (a : Fin n → C(Interval, ↥(OriginalBoundaryArc.openDisk S x R)ᶜ))
    (U : Set S)
    (hU : CurveComplex.HyperellipticModel.IsComplementComponent
      (OriginalBoundaryArc.openDisk S x R ∪
        OriginalBoundaryArc.boundaryCircle S x R ∪ arcTrace a) U) :
    IsOpen U := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  exact original_cut_component_open_of_closed_base a
    (original_disk_union_boundary_closed S g hS x R htarget) hU

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
