import CurveComplexGenusTwo.Topology.ActualThreeArcCount.RegionHomology
import CurveComplexGenusTwo.Topology.ActualThreeArcCount.ExteriorDictionary

open CurveComplex Set Topology CategoryTheory
open CurveComplexGenusTwo.CWHurewicz
open scoped Manifold ContDiff
noncomputable section
namespace CurveComplexGenusTwo.SourceTopology.ThreeArcCut
private abbrev Plane := EuclideanSpace ℝ (Fin 2)

abbrev exterior (S : Type) [TopologicalSpace S]
    [ChartedSpace Plane S] (x : S) (R : ℝ) : Set S :=
  (OriginalBoundaryArc.openDisk S x R)ᶜ

abbrev originalBoundary (S : Type) [TopologicalSpace S]
    [ChartedSpace Plane S] (x : S) (R : ℝ) : Set S :=
  OriginalBoundaryArc.boundaryCircle S x R

abbrev arcTrace {S : Type} [TopologicalSpace S]
    {Q : Set S} {n : ℕ} (a : Fin n → C(Interval, ↥Q)) : Set S :=
  ⋃ i, Set.range (fun t => (a i t).val)


/-- Exact original-source region classification kills the homology image of the
whole literal open cut complement. No finite-cut model is assumed. -/
theorem original_standard_complement_homologyInclusion_zero
    (S : Type) [TopologicalSpace S] [ChartedSpace Plane S]
    (g : ℕ) (hS : IsGenus S g)
    (x : S) (R : ℝ) (hR : 0 < R)
    (htarget : Metric.closedBall ((chartAt Plane x) x) R ⊆
      (chartAt Plane x).target)
    (n : ℕ) (a : Fin n → C(Interval, ↥(exterior S x R)))
    (hregions : ∀ U : Set S,
      CurveComplex.HyperellipticModel.IsComplementComponent
        (OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a) U →
      U ⊆ interior (exterior S x R) →
      DiskRegion (exterior S x R) U ∨
        BoundaryAnnulusRegion (exterior S x R) (originalBoundary S x R) U)
    (k : ℕ) (hk : 0 < k) :
    homologyInclusion S
      (OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a)ᶜ k = 0 := by
  letI : ClosedSurface S := Classical.choice hS.2.1
  letI : LocallyPathConnectedSpace S := ChartedSpace.locallyPathConnectedSpace Plane S
  letI : PathConnectedSpace S := PathConnectedSpace.of_locallyPathConnectedSpace
  let A := OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R ∪ arcTrace a
  have hcore : Aᶜ ⊆ interior (exterior S x R) := by
    rw [OriginalBoundaryArc.exterior_interior_eq_complement_chart_closed_disk S g hS x R hR htarget]
    intro y hy hyb
    exact hy (Or.inl hyb)
  have hA : IsClosed A := by
    have hball : IsCompact ((chartAt Plane x).symm ''
        Metric.closedBall ((chartAt Plane x) x) R) :=
      (isCompact_closedBall _ _).image_of_continuousOn
        ((chartAt Plane x).continuousOn_symm.mono htarget)
    have hbase : OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R =
        (chartAt Plane x).symm '' Metric.closedBall ((chartAt Plane x) x) R := by
      simp only [OriginalBoundaryArc.openDisk, originalBoundary, OriginalBoundaryArc.boundaryCircle,
        ← Set.image_union, Metric.ball_union_sphere]
    change IsClosed ((OriginalBoundaryArc.openDisk S x R ∪ originalBoundary S x R) ∪ arcTrace a)
    rw [hbase]
    apply hball.isClosed.union
    exact isClosed_iUnion_of_finite (fun i =>
      (isCompact_range (continuous_subtype_val.comp (a i).continuous)).isClosed)
  have hn := standardComplement_inclusion_nullhomotopic S x R hR.le htarget
    (exterior S x R) A hA (fun U hU => hregions U hU (hU.2.2.1.trans hcore))
  exact positiveHomologyMap_eq_zero_of_nullhomotopic _ hn k hk

end CurveComplexGenusTwo.SourceTopology.ThreeArcCut
